-module(ty_rec).

-define(debug, true).
-include_lib("sanity.hrl").

% A macro to wrap some term in a closure to be evaluated lazily on-demand
-define(F(Z), fun() -> Z end).

% a type is a pointer to a corecursively defined type node
% depending on the mechanism of detecting 'sameness' of types,
% multiple types with the same denotation can be mapped to the same reference.
% For termination, it is necessary that the Any type and further that some simple boolean tautologies are shared.
% The references start at 0 and increase monotonically.
% Defining a new type can be done by requesting a the next free type reference, which also increases the reference counter by 1.
% Such a new reference must be closed before it can be used.
% If the newly requested type is found to be shared with a previously defined type, 
% the number of the newly requested type is skipped.
-type type() :: {ty_ref, integer()}.

% In addition to the number, a type reference can optionally be 
% equipped with a name. 
% These names are used when user-defined types from
% the Erlang AST are transformed to our internal representation.
-type type_name() :: term(). %TODO decide the structure of type names

% TODO doc
-type type_tbl() :: #{type() => ty()}.
 
% We have at least four options for hash tables in Erlang that are efficient:
% * ETS tables and its derivates
% * (Big) maps (HAMT) with custom collision-handling
% * custom hash table (Erlang)
% * custom hash table (C Nif)
% Whereas implemeting a custom hash table in C would be the most efficient,
% it's unfeasible and likely premature optimization.
% A custom hash table in Erlang is much slower than the Erlang maps implementation which is implemented in C.
% We can't use ETS tables (or similar) since we can't supply our own (constant-time) hash function for comparisons.
% The hashing of deep type terms is too slow which ETS employs.
% Maps in Erlang which are implemented in C and implement the fast hash array mapped tries can instead be used as a base for a custom hash-table implementation.
% We keep these hash-tables in a global state.
% The references to global hash-tables can be kept anywhere.
% We put them in the process dictionary.
-type hash_tbl() :: #{type() => ty()}.

% Names coming from user-defined types are stored in a separate table
% A type can have multiple names associated because of sharing
% TODO we want sharing, but for error messages we ideally don't want sharing
% => this will lose information, discuss
% 
% example construction/transformation of a symbol table: 
% predefined term: any()
% 0 => [term]
% 
% predefined list: [any()]
% 0 => [term]
% 1 => [list]
% 
% -type custom_list() :: [any()]
% 0 => [term]
% 1 => [list, custom_list]
-type name_tbl() :: #{type() => [type_name()]}.

-record(ty, {
  % the reference of this type
  id = open :: integer() | open, 

  % * type variables are encoded in each part of the DNF separately
  % * user defined types are transformed to a new type reference with 
  %   the original user-defined name
  % * Erlang records are tagged tuples

  % pid(), port(), reference(), [], float()
  predef = dnf_var_predef:empty() :: dnf_var_predef:type(), 
  % singleton atoms; they have their own efficient representation
  atom = dnf_var_ty_atom:empty() :: dnf_var_ty_atom:type(), 
  % singleton integers, represented integer intervals with possible open ends (plus/minus infinity)
  interval = dnf_var_int:empty() :: dnf_var_int:type(), 
  % custom type for lists; Erlang lists are not encoded as a (co-)recursive type
  list = dnf_var_ty_list:empty() :: dnf_var_ty_list:type(),
  % n-ary tuples for n >= 0;  {}, {_}, ...
  tuple = {dnf_var:empty(), #{}} :: {dnf_var:type(), dnf_var_ty_tuple:type()}, 
  % n-ary functions for n >= 0; () -> T; (U) -> T; (U, V) -> T; ...
  function = {dnf_var:empty(), #{}} :: {dnf_var:type(), dnf_var_ty_function:type()},

  % ===
  % TODO these are not yet implemented and unused
   
  % dynamic(), ?-type; we could include it in predef, 
  % but dynamic has some special interactions with other parts of the solver (tally, subtyping)
  dynamic = unused, % TODO #DYNAMIC

  % Erlang bitstrings
  % <<E1, E2, ... En>>
  bitstring = unused, % TODO #DYNAMIC

  % unordered Erlang maps with optional and mandatory associations
  % #{t := t, t=> t}
  map = unused % TODO #DYNAMIC
}).
-type ty() :: #ty{}.
-type open_ty() :: #ty{id = open}. % TODO does this type spec mean what I think it does?

% Type API
% The type api for coinductive types has two types of methods
%   1. Methods that start a co-recursive chain
%   2. Methods that continue a co-recursive chain
% We mark 2. methods with a suffix corec.
% The proper order use of 1. and 2. needs to be ensured by the programmer,
% otherwise the algorithm does not terminate.
% The memoization of one chain is not allowed to be reused in 
% another method (2.), a new chain must be started with its own memoization.
% 
% The state is always implicit and kept outside in a shared ETS table.

% constructors for any and empty types, semantic
-export([empty/0, any/0]).

% structural check if a type is equivalent to Any; heuristic
-export([is_any/1]).

% set-theoretic operators on types
-export([negate/1, union/2, intersect/2, difference/2]).

% semantic evaluations on types 
% subtyping algorithm
-export([is_empty/1, is_subtype/2, is_equivalent/2]).
% tallying (phase 1)
-export([normalize/3]).

% constructors
-export([predef/0, predef/1, variable/1, atom/1, interval/1, tuple/2, list/1, function/2, list/0, function/0, atom/0, interval/0, tuple/0]).
% projection
-export([pi/2]).

% other co-recursive functions
-export([
  % collect all variables used in anywhere in the type
  all_variables/1,
  % given a type that consists of a union of (sub-)types, 
  % extract out common variables that are contained in every part of the type
  extract_variables/1,
  % substitution for type variables
  % given a map of variable -> type mappings,
  % return a new type reference with the mappings replaced
  substitute/2,
  % type() -> string() conversion, no simplification
  print/1,
  % Generic walk over the type and apply operations
  transform/2
]).


-type interval() :: term().
%%-type ty_tuple() :: term().
%%-type ty_function() :: term().
-type ty_variable() :: term().
-type ty_atom() :: term().

% ======
% IMPLEMENTATION
% ======
% 
% The state is explicit and can be modified by any function
% The state keeps track of:
% * The next unused ID for a new type
% * The type table, mapping type pointers to type records
% * The hash table for type records to enable structure sharing
% * The name table, mapping types to previously seen aliases
-record(s, {id = 0, type_tbl = #{}, hash_tbl = #{}, name_tbl = #{}}).
-type s() :: #s{}.
 
% The top type is predefined, enforced to be shared and always mapped to reference 0.
-spec any() -> type().
any() -> {ty_ref, 0}.

% The empty type is defined in terms of the any type and negation
-spec empty() -> type().
empty() ->
  negate(any()).

-spec negate(type()) -> type().
negate(Type) ->
  % initializes a corecursive negate operation with a new memoization set on the given type
  % returns a possibly new type with the result and all intermediate created types 
  % added to the implicit state
  corec_nostate([Type], fun(Unfoldable, Unfolded, Memo) -> 
    new_type(Unfoldable, Unfolded, Memo, fun negate_ty/2)
  end).

-spec negate_ty([ty()], memo()) -> open_ty().
negate_ty(
  [#ty{predef = P,atom = A,interval = I,list = L,tuple = {DT, T},function = {DF, F},dynamic = _D,bitstring = _B,map = _M}], 
  Memo) ->
  #ty{
        predef = dnf_var_predef:negate(P),
        atom = dnf_var_ty_atom:negate(A),
        interval = dnf_var_int:negate(I),
        list = dnf_var_ty_list:negate(L, Memo),
        tuple = {dnf_var:negate(DT, Memo), maps:map(fun(_K,V) -> dnf_var_ty_tuple:negate(V, Memo) end, T)},
        function = {dnf_var:negate(DF, Memo), maps:map(fun(_K,V) -> dnf_var_ty_function:negate(V, Memo) end, F)}
        % dynamic = ... % TODO #DYNAMIC
        % bitstring = ... % TODO #BITSTRING
        % map = ... % TODO #MAP
    }.

-spec intersect(type(), type()) -> type().
intersect(Type1, Type2) ->
  corec_nostate([Type1, Type2], fun(Unfoldable, Unfolded, Memo) -> 
    new_type(Unfoldable, Unfolded, Memo, fun intersect_ty/2)
  end).

-spec intersect_ty([ty(), ty()], memo()) -> open_ty().
intersect_ty([
  #ty{predef = P1,atom = A1,interval = I1,list = L1,tuple = T1,function = F1,dynamic = _D1,bitstring = _B1,map = _M1}, 
  #ty{predef = P2,atom = A2,interval = I2,list = L2,tuple = T2,function = F2,dynamic = _D2,bitstring = _B2,map = _M2}
], Memo) ->
  #ty{
    predef = dnf_var_predef:intersect(P1, P2),
    atom = dnf_var_ty_atom:intersect(A1, A2),
    interval = dnf_var_int:intersect(I1, I2),
    list = dnf_var_ty_list:intersect(L1, L2, M),
    tuple = multi_intersect(T1, T2, M),
    function = multi_intersect_fun(F1, F2, M)
    % dynamic = ... % TODO #DYNAMIC
    % bitstring = ... % TODO #BITSTRING
    % map = ... % TODO #MAP
  }.

% TODO measure if caching difference and union increases performance (even though intersect and negate is cached already)
-spec difference(type(), type()) -> type().
difference(A, B) ->
  intersect(A, negate(B)).

-spec union(type(), type()) -> type().
union(A, B) ->
  negate(intersect(negate(A), negate(B))).

% TODO caching
-spec is_empty(type()) -> boolean().
is_empty(Type) -> 
  corec_nostate([Type], fun(Unfoldable, Unfolded, Memo) -> 
    % emptyness does not need state and assumes an already visited type is empty 
    is_empty_ty(Unfolded, Memo#{Unfoldable => true})
  end).

% TODO in CDuce, is_any checks are used to keep the leafs of BDDs uniform; do we need this?
-spec is_any(type()) -> boolean().
is_any(Type) -> case any() of Type -> true; _ -> false end.

-spec is_subtype(type(), type()) -> boolean().
is_subtype(Type1, Type2) ->
  is_empty(intersect(Type1, negate(Type2))).

-spec is_equivalent(type(), type()) -> boolean().
is_equivalent(Type1, Type2) ->
  is_subtype(Type1, Type2) andalso is_subtype(Type2, Type1).

% TODO type spec 
% TODO corec
-type set_of_constraint_sets() :: list(list(term())). % TODO
-spec normalize(type(), term(), memo()) -> set_of_constraint_sets().
normalize(Type, Fixed, M) ->
  corec_nostate([Type], fun(Unfoldable, Unfolded, Memo) ->
    % line 1 Figure 3, popl part 2 paper, the codefinition of normalization is the (set of the) unsatisfiable constraint set
    NewMemo = Memo#{{Unfoldable, Fixed} => [[]]}, %TODO use socs api
    normalize_ty(Unfolded, Fixed, NewMemo)
  end).

-spec predef(dnf_var_predef:type()) -> type().
predef(Predef) ->
  store(#ty{predef = Predef}).

-spec predef() -> type().
predef() -> predef(dnf_var_predef:any()).

-spec variable(ty_variable()) -> type().
variable(Var) ->
  Any = load(any()),
  store(Any#ty{
    id = open,
    predef = dnf_var_predef:intersect(Any#ty.predef, dnf_var_predef:var(Var)),
    atom = dnf_var_ty_atom:intersect(Any#ty.atom, dnf_var_ty_atom:var(Var)),
    interval = dnf_var_int:intersect(Any#ty.interval, dnf_var_int:var(Var)),
    list = dnf_var_ty_list:intersect(Any#ty.list, dnf_var_ty_list:var(Var)),
    tuple = {dnf_var:var(Var), #{}},
    function ={dnf_var:var(Var), #{}}
  }).

-spec atom(ty_atom()) -> type().
atom(Atom) ->
  store(#ty{atom = Atom}).

-spec atom() -> type().
atom() -> atom(dnf_var_ty_atom:any()).

list() -> list(dnf_var_ty_list:any()).
list(List) ->
  store(#ty{list = List}).

-spec interval(interval()) -> type().
interval(Interval) ->
  store(#ty{interval = Interval}).

-spec interval() -> type().
interval() -> interval(dnf_var_int:any()).

% {default, [Int]}, tuple :: 
%    Default for all tuple sizes except the ones specified with Sizes; those are initialized as empty
% Int, tuple :: 
%   Tuple constructor for that exact size
-spec tuple({default, [integer()]}, dnf_var:type()) -> type();
(integer(), dnf_var_ty_tuple:type()) -> type().
tuple({default, Sizes}, DefaultVars) ->
  NotCaptured = maps:from_list(lists:map(fun(Size) -> {Size, dnf_var_ty_tuple:empty()} end, Sizes)),
  store(#ty{tuple = {DefaultVars, NotCaptured}});
tuple(ComponentSize, Tuple) ->
  store(#ty{tuple = {dnf_var:empty(), #{ComponentSize => Tuple}}}).

-spec tuple() -> type().
tuple() ->
  store(#ty{tuple = {dnf_var:any(), #{}}}).

-spec function({default, [integer()]}, dnf_var:type()) -> type();
(integer(), dnf_var_ty_function:type()) -> type().
function({default, Sizes}, DefaultVars) ->
  NotCaptured = maps:from_list(lists:map(fun(Size) -> {Size, dnf_var_ty_function:empty()} end, Sizes)),
  store(#ty{function = {DefaultVars, NotCaptured}});
function(ComponentSize, Fun) ->
  store(#ty{function = {dnf_var:empty(), #{ComponentSize => Fun}}}).

-spec function() -> type().
function() ->
  store(#ty{function = {dnf_var:any(), #{}}}).

% Projections for components of the type
% TODO #DYNAMIC
% TODO #BITSTRING
% TODO #MAP
-spec pi
(predef, type()) -> dnf_var_predef:type();
(atom, type()) -> dnf_var_ty_atom:type();
(interval, type()) -> dnf_var_int:type();
(list, type()) -> dnf_var_ty_list:type();
(tuple, type()) -> {dnf_var:type(), #{integer() => dnf_var_ty_tuple:type()}};
(function, type()) -> {dnf_var:type(), #{integer() => dnf_var_ty_function:type()}};
({tuple, default}, type()) -> dnf_var:type();
({tuple, integer()}, type()) -> dnf_var_ty_tuple:type();
({function, default}, type()) -> dnf_var:type();
({function, integer()}, type()) -> dnf_var_ty_function:type().
pi(atom, TyRef) ->
  Ty = type:load(TyRef),
  Ty#ty.atom;
pi(interval, TyRef) ->
  Ty = type:load(TyRef),
  Ty#ty.interval;
pi(list, TyRef) ->
  Ty = type:load(TyRef),
  Ty#ty.list;
pi(tuple, TyRef) ->
  Ty = type:load(TyRef),
  Ty#ty.tuple;
pi({tuple, default}, TyRef) ->
  Ty = type:load(TyRef),
  {D, _TM} = Ty#ty.tuple,
  D;
pi({tuple, Len}, TyRef) ->
  Ty = type:load(TyRef),
  {D, TM} = Ty#ty.tuple,
  maps:get(Len, TM, D);
pi({function, default}, TyRef) ->
  Ty = type:load(TyRef),
  {D, _TM} = Ty#ty.function,
  D;
pi({function, Len}, TyRef) ->
  Ty = type:load(TyRef),
  {D, TM} = Ty#ty.function,
  maps:get(Len, TM, D);
pi(predef, TyRef) ->
  Ty = type:load(TyRef),
  Ty#ty.predef;
pi(function, TyRef) ->
  Ty = type:load(TyRef),
  Ty#ty.function.

% TODO this should be a co-recursive function
-spec all_variables(type()) -> [ty_variable:type()].
all_variables(Type) ->
  corec_nostate([Type], fun(Unfoldable, Unfolded, Memo) -> 
    % memo: variables of a previously seen type have already been collected
    all_variables_ty(Unfolded, Memo#{Unfoldable => []})
  end).

% TODO #DYNAMIC
% TODO #BITSTRING
% TODO #MAP
all_variables_ty([#ty{
    predef = Predefs,
    atom = Atoms,
    interval = Ints,
    list = Lists,
    tuple = Tuples,
    function = Functions
  }], Memo) ->

  lists:usort(dnf_var_predef:all_variables(Predefs)
  ++ dnf_var_ty_atom:all_variables(Atoms)
  ++ dnf_var_int:all_variables(Ints)
  ++ dnf_var_ty_list:all_variables(Lists, Memo)
  ++ dnf_var_ty_tuple:mall_variables(Tuples, Memo)
  ++ dnf_var_ty_function:mall_variables(Functions, Memo)).


% TODO #DYNAMIC
% TODO #BITSTRING
% TODO #MAP
% TODO doc not corecursive explain why
-spec extract_variables(type()) -> {[ty_variable:type()], type()}.
extract_variables(Type) ->
  #ty{predef = P, atom = A, interval = I, list = L, tuple = T, function = F} = load(Type),

  % TODO this can be implemented more efficiently
  % Current procedure:
  %  1. Collect all variables in all parts
  %  2. Check if a variable is contained in the union of parts
  %  3. If so, that variable can be extracted and removed from the union of parts
  %  4. Do so for all variables
  PossibleVars = lists:foldl(fun(E, Acc) ->
    sets:intersection(sets:from_list(E), Acc)
              end, 
    sets:from_list(dnf_var_predef:all_variables(P)),
    [
      dnf_var_ty_atom:all_variables(A),
      dnf_var_int:all_variables(I),
      dnf_var_ty_list:all_variables(L, #{}),
      dnf_var_ty_tuple:mall_variables(T, #{}),
      dnf_var_ty_function:mall_variables(F, #{})
    ]),


  {Vars, NewTy} = lists:foldl(fun(Var, {ExtractedVars, TTy}) ->
    case is_subtype(variable(Var), TTy) of
      true ->
        {[Var | ExtractedVars],
        diff(TTy, variable(Var))};
      false -> {ExtractedVars, TTy}
    end
                      end, {[], Type}, sets:to_list(PossibleVars)),

  {Vars, NewTy}.

% TODO type of map
-spec substitute(type(), term()) -> type().
substitute(Type, SubstituteMap) ->
  % TODO TIME
  % ?TIME(substitute, substitute(TyRef, SubstituteMap, #{})).
  corec_nostate([Type], fun(Unfoldable, Unfolded, Memo) -> 
    new_type(Unfoldable, Unfolded, Memo, fun(Unfolded0, Memo0) -> substitute_ty(Unfolded0, SubstituteMap, Memo0) end)
  end).

% converts a type to a string representation
-spec print(type()) -> string().
% print(Ref) -> pretty:render_ty(ast_lib:erlang_ty_to_ast(Ref)) .
print(Type = {ty_ref, Id}) -> 
  % Str = pretty:format([], [Ty], #{}),
  % collect all types
  AllTypes = corec_fun([Ty], _AllTypesState = [], #{}, fun print_corec/2, fun([Ref], State) -> {[Ref], State} end).
  

print_corec([Ty = {ty_ref, _}], Memo) -> 
  "RESULT := " ++
  corec_fun([Ty], Memo, fun print_corec/2, fun([{ty_ref, Id}]) -> integer_to_list(Id) end);
print_corec([#ty{predef = P,atom = A,interval = I,list = L,tuple = T,function = F,dynamic = D,bitstring = B,map = Map}], Memo) ->
  "ty{}".


% TODO spec 
% TODO doc 
% TODO co-rec
-spec transform(type(), #{}) -> term().
transform(TyRef, Ops) ->
  % Do things twice, pos and neg
  Pos = transform_p(TyRef, Ops),
  Neg = transform_p(ty_rec:negate(TyRef), Ops),

%%  io:format(user, "Positive:~n~p~n", [Pos]),
%%  io:format(user, "Negative:~n~p~n", [Neg]),
  % very dumb heuristic: smaller is better
  case
    size(term_to_binary(Pos)) > size(term_to_binary(Neg))
  of
    false -> {pos, Pos};
    _ ->
      % fix1: any is smaller than none, pick none anyway
      case stdtypes:tnone() of
        Pos -> {pos, Pos};
        _ -> {neg, Neg}
      end
  end.

  















% ===
% PRIVATE FUNCTIONS
% ===

% TODO benchmark against 'direct' implementation of corecursive functions
% wrapper for corec without state

% A generic corecursion operator for type operators negation/union/intersection 
% and other constant corecursive functions (is_empty)
% We track the codefinition inside the memoization map
% If a corecursive call is encountered, use the mapped codefinition in the map
% The operator provides two ways of specifying memoization: 
% a constant term memoization (used for e.g. is_empty, Boolean return) 
% and a new equation reference memoization (used for e.g. type operators)
-type unfoldable() :: [type()].
-type unfolded() :: [ty()].
-type state() :: term().
-type memo() :: #{}.
-spec 
% ([unfoldable()], state(), memo(), fun(([unfolded()], state(), memo()) -> {ty(), state()})) -> {type(), State};
corec(
  unfoldable(),   % unfoldable
  state(),        % state
  memo(),         % memo
  fun((unfoldable(), unfolded(), state(), memo()) -> {X, state()})
) -> {X, state()}.
corec(Unfoldable, State, Memo, Continue) ->
 #s{type_tbl = Tys} = state(),
 case Memo of
  % memoization, terminate and return co-definition
   #{Unfoldable := Codefinition} -> Codefinition;
   _ -> 
     UnfoldList = fun(L) -> 
      % TODO is it more efficient to get all elements from a map at once?
      % this means defining corec for 0,1, and 2 argument functions
      % measure runtime benefit, then maybe split
      % given a list of types, fetch their type record from the given type_tbl
      [begin #{T := Ty} = Tys, Ty end || T <- L] 
      end,
     Unfolded = UnfoldList(Unfoldable),
     Continue(Unfoldable, Unfolded, State, Memo)
    %  NewMemo = SetCodefinition(Memo, Types),
    %  Continue(Unfolded, State, NewMemo)
    %  case Option of 
    %    reference -> 
    %     NewId = new_id(),
    %     NewMemo =  Memo#{Types => NewId},
    %     {Ty, NewState} = Continue(UnfoldedTypes, State, NewMemo),

    %     % store new type record
    %     % store may return something other than the given NewId if sharing is employed
    %     {store(NewId, Ty), NewState};
    %    % 'unfold' the input(s), memoize the constant term, and apply Continue
    %    {const, Const} -> 
    %     Continue(UnfoldedTypes, State, Memo#{Types => Const})
    %  end
 end.

corec(Unfoldable, Memo, Continue) ->
  {Result, no_state} = corec(Unfoldable, no_state, Memo, fun(Unfoldable, Unfolded, no_state, Memo) -> {Continue(Unfoldable, Unfolded, Memo), no_state} end),
  Result.

corec_nostate(Unfoldable, Continue) ->
  corec(Unfoldable, #{}, Continue).

corec_state(Unfoldable, State, Continue) ->
  corec(Unfoldable, State, #{}, Continue).

load({ty_ref, Id}) ->
  #s{type_tbl = #{Id := Ty}} = state(),
  Ty.

store(OldTy = #ty{id = open}) ->
  NewId = new_id(),
  store(NewId, OldTy).

% preconditions: 
% id = open
store(NewId, OldTy = #ty{id = open}) ->
  (S = #s{hash_tbl = Htbl, type_tbl = Tys}) = state(),
  Ty = OldTy#ty{id = NewId},
  H = hash(Ty),
  case Htbl of
    #{H := Refs} -> 
      % a good hash function should produce a lot of share hits and close to no collisions
      case 
        % TODO horrible, refactor
        [X || X <- Refs, 
          begin 
            % structural compare the parts of the type to store and possible stored references
            % TODO explain why ID is not used in comparison and 
            % why only non-recursive types can be shared with this method
            #{X := XTy } = Tys, 
            OldTy =:= XTy#ty{id = open}
          end] 
          of
        [Ref] -> 
          io:format(user, "Share hit for ~p!~n", [Ref]),
          Ref;
        _ -> 
          NewTy = Ty#ty{id = NewId},
          io:format(user, "Store ~p:= (collision)~n~p~n", [NewId, NewTy]),
          % update hash table and type table with new entry
          % the hash table is updated in the collision slot
          NewState = S#s{
            hash_tbl = Htbl#{H => Refs ++ [{ty_ref, NewId}]}, 
            type_tbl = Tys#{{ty_ref, NewId} => NewTy}
          },
          ok = update_state(NewState),
          {ty_ref, NewId}
        end;
    _ ->
      NewTy = Ty#ty{id = NewId},
      io:format(user, "Store ~p:~n~p~n", [NewId, NewTy]),
      % update hash table and type table with new entry
      NewState = S#s{
        hash_tbl = Htbl#{H => [{ty_ref, NewId}]}, 
        type_tbl = Tys#{{ty_ref, NewId} => NewTy}
      },
      ok = update_state(NewState),
      {ty_ref, NewId}
    end.

% TODO hash functions
% 1. erlang:phash2
% 2. Cduce
% 3. hashing modulo alpha-equivalence
% Measure against test suite then replace hash function with better one
hash(#ty{id = Id}) ->
  % sanity check, only hash valid types
  true = (Id /= open),
  % bad hash function
  17.

-spec state() -> s().
state() ->
  State = get(state),
  case State of
    undefined -> empty_state();
    _ -> State
  end.

-spec empty_state() -> s().
empty_state() ->
  % define the Any type to be globally known
  Any = {ty_ref, 0},
  % we define the corecursive type and close it at the same time.
  % in other representations, 
  % we would need to define the Empty type at the same time since they are mutually recurive
  % Any = (Empty -> Any) U ...
  % Empty = !Any
  % here, since all functions are represented as a default bdd_bool value 1,
  % we don't need an explicitly defined Empty type
  AnyRec = #ty{
    id = 0,
    predef = dnf_var_predef:any(),
    atom = dnf_var_ty_atom:any(),
    interval = dnf_var_int:any(),
    list = dnf_var_ty_list:any(),
    tuple = {dnf_var:any(), #{}},
    function = {dnf_var:any(), #{}},
    dynamic = bdd_bool:any(),
    bitstring = bdd_bool:any(),
    map = bdd_bool:any()
  },

  
  #s{
    id = 1, 
    type_tbl = #{Any => AnyRec}, 
    hash_tbl = #{ hash(AnyRec) => [Any] }
  }.

-spec update_state(s()) -> ok.
update_state(S) ->
  put(state, S),
  ok.

new_id() -> 
  (S = #s{id = Id}) = state(),
  ok = update_state(S#s{id = Id + 1}),
  Id.


% type() -> type()
% type(), type() -> type()
% type() -> string()
% type() -> [type()]

% [type()], memo(), 

% This definition is used to continue a (nested) corecursive negation
% -spec negate_corec([type()], corec_state(), memo()) -> {type(), corec_state()}; ([ty()], term(), memo()) -> ty().
% negate_corec([Type = {ty_ref, _}], Memo) -> 
%   corec_ref(Type, State, Memo, fun negate_corec/2);
% negation delegates the operation to its components.
% components that could be co-inductive are supplied with the current memoization set

% This definition is used to continue a (nested) corecursive intersection
-spec intersect_corec(type(), term(), memo()) -> type(); (ty(), term(), memo()) -> ty().
intersect_corec([Type1 = {ty_ref, _}, Type2], Memo) -> corec_ref([Type1, Type2], Memo, fun negate_corec/2);
% negation delegates the operation to its components.
% components that could be co-inductive are supplied with the current memoization set
intersect_corec([
  #ty{predef = P1,atom = A1,interval = I1,list = L1,tuple = T1,function = F1,dynamic = D1,bitstring = B1,map = Map1}, 
  #ty{predef = P2,atom = A2,interval = I2,list = L2,tuple = T2,function = F2,dynamic = D2,bitstring = B2,map = Map2}
], M) ->
  type:store(#ty{
    predef = dnf_var_predef:intersect(P1, P2),
    atom = dnf_var_ty_atom:intersect(A1, A2),
    interval = dnf_var_int:intersect(I1, I2),
    list = dnf_var_ty_list:intersect(L1, L2, M),
    tuple = multi_intersect(T1, T2, M),
    function = multi_intersect_fun(F1, F2, M),
    % TODO implement
    % TODO doc and tag issues
    dynamic = bdd_bool:intersect(D1, D2),
    bitstring = bdd_bool:intersect(B1, B2), %TODO do bitstrings need memo?
    map = bdd_bool:intersect(Map1, Map2) % should be supplied with the memo set
  }).

-spec is_empty_ty([type()], memo()) -> boolean().
is_empty_ty([#ty{predef = P,atom = A,interval = I,list = L,tuple = T,function = F,dynamic = _D,bitstring = _B,map = _Map}], Memo) ->
  dnf_var_predef:is_empty(P)
    andalso dnf_var_ty_atom:is_empty(A)
    andalso dnf_var_int:is_empty(I)
    % andalso ?:is_empty(D) % TODO #DYNAMIC
    % andalso ?:is_empty(B) % TODO #BITSTRING
    % andalso ?:is_empty(Map) %  TODO #MAP
    andalso dnf_var_ty_list:is_empty(L, Memo)
    andalso multi_empty_tuples(T, Memo)
    andalso multi_empty_functions(F, Memo).


% ========
% TODO
% ========

new_type(Unfoldable, Unfolded, Memo, Continue) ->
  NewId = new_id(),
  NewTy = Continue(Unfolded, Memo#{Unfoldable => NewId}),
  store(NewId, NewTy).

maybe_intersect(Z2, Other, Intersect) ->
  case subty:is_subty(symtab:empty(), Z2, Other) of %TODO symtab?
    true -> Z2;
    false -> Intersect([Other, Z2])
  end.


transform_p(TyRef, Ops =
  #{
    any_list := Lists,
    any_tuple := Tuples,
    any_function := Functions,
    any_int := Intervals,
    any_atom := Atoms,
    any_predef := Predef,
    union := Union,
    intersect := Intersect,
    negate := Negate,
    var := Var
  }) ->
%%  io:format(user,"<~p> Transforming: ~p~n~p~n", [Ref = make_ref(), TyRef, ty_ref:load(TyRef)]),
  DnfMap = prepare(TyRef),
%%  io:format(user, "<~p> Prepared: ~n~p~n", [Ref, DnfMap]),

  Mapped = maps:map(fun({Pv, Nv}, TyR) ->
    NewVars = lists:map(fun(K) -> Var(K) end, Pv),
    NewVarsN = lists:map(fun(K) -> Negate(Var(K)) end, Nv),
    case ty_rec:is_subtype(ty_rec:any(), TyR) of
      true ->
        Intersect(NewVars ++ NewVarsN);
      _ ->
        #ty{predef = P, atom = A, interval = I, list = L, tuple = {DT, T}, function = {DF, F}} = ty_ref:load(TyR),
        NP = maybe_intersect(dnf_var_predef:transform(P, Ops), Predef(), Intersect),
        NA = maybe_intersect(dnf_var_ty_atom:transform(A, Ops), Atoms(), Intersect),
        NI = maybe_intersect(dnf_var_int:transform(I, Ops), Intervals(), Intersect),
        NL = maybe_intersect(dnf_var_ty_list:transform(L, Ops), Lists(), Intersect),

        Z1 = multi_transform(DT, T, Ops),
        NT = maybe_intersect(Z1, Tuples(), Intersect),

        Z2 = multi_transform_fun(DF, F, Ops),
        NF = maybe_intersect(Z2, Functions(), Intersect),
        Intersect(NewVars ++ NewVarsN ++ [Union([NP, NA, NI, NL, NT, NF])])
    end
           end, DnfMap),

  Ety = Union(maps:values(Mapped)),
%%  io:format(user,"<~p> Result: ~p~n", [Ref, Ety]),
  Sanity = ast_lib:ast_to_erlang_ty(Ety),
%%  io:format(user,"<~p> Sanity: ~p~n", [Ref, Sanity]),
  % leave this sanity check for a while
  case is_equivalent(TyRef, Sanity) of
    true -> ok;
    false ->
      io:format(user, "--------~n", []),
      io:format(user, "~p~n", [ty_ref:load(TyRef)]),
      io:format(user, "~p~n", [Ety]),
      error(todo)
  end,
  Ety.

% TODO refactor this properly it's ugly
prepare(TyRef) ->
  #ty{predef = P, atom = A, interval = I, list = L, tuple = {DT, T}, function = {DF, F}} = ty_ref:load(TyRef),
  VarMap = #{},

  PDnf = dnf_var_predef:get_dnf(P),
  ADnf = dnf_var_ty_atom:get_dnf(A),
  IDnf = dnf_var_int:get_dnf(I),
  LDnf = dnf_var_ty_list:get_dnf(L),

  PMapped = lists:map(fun({Pv, Nv, Ty}) -> {{Pv, Nv}, ty_rec:predef(dnf_var_predef:predef(Ty))} end, PDnf),
  AMapped = lists:map(fun({Pv, Nv, Ty}) -> {{Pv, Nv}, ty_rec:atom(dnf_var_ty_atom:ty_atom(Ty))} end, ADnf),
  IMapped = lists:map(fun({Pv, Nv, Ty}) -> {{Pv, Nv}, ty_rec:interval(dnf_var_int:int(Ty))} end, IDnf),
  LMapped = lists:map(fun({Pv, Nv, Ty}) -> {{Pv, Nv}, ty_rec:list(dnf_var_ty_list:list(Ty))} end, LDnf),


  TupleMapped = lists:map(fun({Pv, Nv, Tp}) -> {{Pv, Nv}, ty_rec:tuple({default, maps:keys(T)}, dnf_var_ty_tuple:tuple(Tp))} end, dnf_var_ty_tuple:get_dnf(DT)),
  TupleExplicitMapped = lists:flatten(lists:map(fun({Size, Tuple}) ->
    DnfTuples = dnf_var_ty_tuple:get_dnf(Tuple),
    _DnfTupleMapped = lists:map(fun({Pv, Nv, Tp}) -> {{Pv, Nv}, ty_rec:tuple(Size, dnf_var_ty_tuple:tuple(Tp))} end, DnfTuples)
                                  end, maps:to_list(T))),

  FunctionMapped = lists:map(fun({Pv, Nv, Tp}) -> {{Pv, Nv}, ty_rec:function({default, maps:keys(F)}, dnf_var_ty_function:function(Tp))} end, dnf_var_ty_function:get_dnf(DF)),
  FunctionExplicitMapped = lists:map(fun({Size, Function}) ->
    DnfFunctions = dnf_var_ty_function:get_dnf(Function),
    _DnfFunctionMapped = lists:map(fun({Pv, Nv, Tp}) -> {{Pv, Nv}, ty_rec:function(Size, dnf_var_ty_function:function(Tp))} end, DnfFunctions)
                                     end, maps:to_list(F)),

  AllKinds = lists:flatten([PMapped, AMapped, IMapped, LMapped, TupleMapped, FunctionMapped, TupleExplicitMapped, FunctionExplicitMapped]),

  UpdateKey = fun(_Key, Ty1, Ty2) -> ty_rec:union(Ty1, Ty2) end,
  AllUnions = lists:foldl(fun({VarKey, Ty}, CurrentMap) ->
    NewMap = #{VarKey => Ty},
    maps:merge_with(UpdateKey, CurrentMap, NewMap)
                          end, VarMap, AllKinds),

%%  io:format(user,"All unions;~n~p~n", [AllUnions]),
  Phase1 = fun Loop(Map) ->
    Res = catch maps:fold(fun({Pv, Nv}, Ty, CurrentMap) -> subsume_variables(Pv, Nv, Ty, CurrentMap) end, Map, Map),
    case Res of
      {modified, NewMap} -> Loop(NewMap);
      _ -> Res
    end
           end,
  SubsumedUnions1 = Phase1(AllUnions),

  % TODO repeat phase2 like phase1
  SubsumedUnions2 = maps:fold(fun({Pv, Nv}, Ty, CurrentMap) ->
    subsume_coclauses(Pv, Nv, Ty, CurrentMap)
                             end, SubsumedUnions1, SubsumedUnions1),

%%  io:format(user, "All: ~n~p~n", [AllUnions]),
%%  io:format(user, "Subsumed: ~n~p~n", [SubsumedUnions]),
%%  io:format(user, "Subsumed all: ~n~p~n", [SubsumedUnions2]),

  % Distribute top types to all variables redundantly, if any
  % atom() | a & (Any \ atom) => atom() | a
  TopTypes = [ty_rec:atom(), ty_rec:interval(), ty_rec:tuple(), ty_rec:function(), ty_rec:list(), ty_rec:predef()],
  NoVarsType = maps:get({[], []}, SubsumedUnions2, ty_rec:empty()),

  RedundantUnions = lists:foldl(fun(Top, Acc) ->
    case ty_rec:is_subtype(Top, NoVarsType) of
      true ->
        maps:map(fun(_, V) -> ty_rec:union(Top, V) end, Acc);
      _ -> Acc
    end
                                end, SubsumedUnions2, TopTypes),

  RedundantUnions.


subsume_variables(Pv, Nv, T, VarMap) ->
  maps:fold(fun({Pv1, Nv1}, T1, CurrentMap) ->
    case {Pv1, Nv1, T1} of
      {Pv, Nv, T} ->
        CurrentMap; % skip, same entry
      _ ->
        maybe_remove_redundant_negative_variables(CurrentMap, T1, T, Pv, Nv, Pv1, Nv1)
    end
            end, VarMap, VarMap).


subsume_coclauses(Pv, Nv, T, VarMap) ->
   maps:fold(fun({Pv1, Nv1}, T1, CurrentMap) ->
    case {Pv1, Nv1, T1} of
      {Pv, Nv, T} -> CurrentMap; % skip, same entry
      _ -> maybe_remove_subsumed_coclauses(CurrentMap, {Pv, Nv, T}, {Pv1, Nv1, T1})
    end
             end, VarMap, VarMap).

maybe_remove_subsumed_coclauses(CurrentMap, _CurrentCoclause = {Pv, Nv, T}, _OtherCoclause = {Pv1, Nv1, T1}) ->
  S = fun(E) -> sets:from_list(E) end,
  % other variables in current variables
  % other neg variables in current neg variables
  % other ty in current ty
  % => remove other coclause
%%  io:format(user,"Check current~n~p~n against other ~n~p~n", [{Pv, Nv, T}, {Pv1, Nv1, T1}]),
  case sets:is_subset(S(Pv), S(Pv1)) andalso sets:is_subset(S(Nv), S(Nv1)) andalso ty_rec:is_subtype(T1, T) of
    true ->
%%      io:format(user, "Removing~n~p~n because ~n~p~n is bigger from current map: ~p~n", [{Pv1, Nv1, T1}, {Pv, Nv, T}, CurrentMap]),
      maps:remove({Pv1, Nv1}, CurrentMap);
    _ ->
      CurrentMap
  end.


maybe_remove_redundant_negative_variables(CurrentMap, T1, T, Pv, Nv, Pv1, Nv1) ->
  S = fun(E) -> sets:from_list(E) end,
  % if other dnf is subtype of current dnf,
  % remove all other negative variables that are in the current positive variables
%%  io:format(user,"Clause ~p~n", [{Pv, Nv, T}]),
%%  io:format(user,"Other Clause ~p~n", [{Pv1, Nv1, T1}]),
%%  io:format(user,"Check~n~p <: ~p~n~p in ~p~n~p in ~p~n", [T1, T, Pv, Nv1, Nv, Nv1]),
  case
    ty_rec:is_subtype(T1, T)
      andalso sets:is_subset(S(Pv), S(Nv1))
      andalso sets:is_subset(S(Nv), S(Nv1 -- Pv))
      andalso sets:is_subset(S(Pv1), S(Pv))
  of
    true ->
      NewMap = maps:remove({Pv1, Nv1}, CurrentMap),
      NewKey = {Pv1, Nv1 -- Pv},
      OldValue = maps:get(NewKey, CurrentMap, ty_rec:empty()),
      NewValue = ty_rec:union(OldValue, T1),
%%      io:format(user, "Removing subsumed positive variable ~p from ~n~p~nResulting in ~p~n", [Pv, {Pv1, Nv1}, NewValue]),
      NewNewMap = maps:put(NewKey, NewValue, NewMap),
      % FIXME skip this case instead
      case NewNewMap == CurrentMap of
        true -> NewNewMap;
        _ -> throw({modified, NewNewMap})
      end;
    false ->
      case
        ty_rec:is_equivalent(T1, T)
          andalso sets:is_subset(S(Pv), S([]))
          andalso Pv1 == Nv
      of
        true ->
          NewMap = maps:remove({Pv1, Nv1}, CurrentMap),
          NewKey = {Pv1 -- Nv, Nv1},
          OldValue = maps:get(NewKey, CurrentMap, ty_rec:empty()),
          NewValue = ty_rec:union(OldValue, T1),
          NewNewMap = maps:put(NewKey, NewValue, NewMap),
          % FIXME skip this case instead
          case NewNewMap == CurrentMap of
            true -> NewNewMap;
            _ -> throw({modified, NewNewMap})
          end;
        false ->
          CurrentMap
      end
  end.


multi_transform(DefaultT, T, Ops = #{any_tuple_i := Tuple, any_tuple := Tuples, negate := Negate, union := Union, intersect := Intersect}) ->
  X1 = dnf_var_ty_tuple:transform(DefaultT, Ops),
  Xs = lists:map(fun({_Size, Tup}) ->
    % if a tuple is semantically equivalent to empty, return empty instead of the empty tuple
    case dnf_var_ty_tuple:is_empty(Tup) of
      true -> dnf_var_ty_tuple:transform(dnf_var_ty_tuple:empty(), Ops);
      _ -> dnf_var_ty_tuple:transform(Tup, Ops)
    end
                 end, maps:to_list(T)),
  Sizes = maps:keys(T),

  DefaultTuplesWithoutExplicitTuples = Intersect([X1, Tuples(), Negate(Union([Tuple(I) || I <- Sizes]))]),
  Union([DefaultTuplesWithoutExplicitTuples, Union(Xs)]).

multi_transform_fun(DefaultF, F, Ops = #{any_function_i := Function, any_function := Functions, negate := Negate, union := Union, intersect := Intersect}) ->
  X1 = dnf_var_ty_function:transform(DefaultF, Ops),
  Xs = lists:map(fun({_Size, Func}) -> dnf_var_ty_function:transform(Func, Ops) end, maps:to_list(F)),
  Sizes = maps:keys(F),

  DefaultFunctionsWithoutExplicitFunctions = Intersect([X1, Functions(), Negate(Union([Function(I) || I <- Sizes]))]),
  Union([DefaultFunctionsWithoutExplicitFunctions, Union(Xs)]).

multi_intersect({DefaultT1, T1}, {DefaultT2, T2}, M) ->
  % get all keys
  AllKeys = maps:keys(T1) ++ maps:keys(T2),
  IntersectKey = fun(Key) ->
    dnf_var_ty_tuple:intersect(
      maps:get(Key, T1, dnf_var_ty_tuple:from_default(DefaultT1)),
      maps:get(Key, T2, dnf_var_ty_tuple:from_default(DefaultT2)),
      M
    )
                 end,
  {dnf_var:intersect(DefaultT1, DefaultT2, M), maps:from_list([{Key, IntersectKey(Key)} || Key <- AllKeys])}.

multi_intersect_fun({DefaultF1, F1}, {DefaultF2, F2}, M) ->
  % get all keys
  AllKeys = maps:keys(F1) ++ maps:keys(F2),
  IntersectKey = fun(Key) ->
    dnf_var_ty_function:intersect(
      maps:get(Key, F1, dnf_var_ty_function:from_default(DefaultF1)),
      maps:get(Key, F2, dnf_var_ty_function:from_default(DefaultF2)),
      M
    )
                 end,
  {dnf_var:intersect(DefaultF1, DefaultF2, M), maps:from_list([{Key, IntersectKey(Key)} || Key <- AllKeys])}.



multi_empty_tuples({Default, AllTuples}, M) ->
  dnf_var:is_empty(Default, M)
    andalso
  maps:fold(fun(_Size, V, Acc) -> Acc andalso dnf_var_ty_tuple:is_empty(V, M) end, true, AllTuples).

multi_empty_functions({Default, AllFunctions}, M) ->
  dnf_var:is_empty(Default, M)
    andalso
    maps:fold(fun(_Size, V, Acc) -> Acc andalso dnf_var_ty_function:is_empty(V, M) end, true, AllFunctions).



normalize_ty(Ty, Fixed, M) ->
  % TODO bitstrings
  % TODO dynamic
  % TODO maps
  PredefNormalize = dnf_var_predef:normalize(Ty#ty.predef, Fixed, M),
  AtomNormalize = dnf_var_ty_atom:normalize(Ty#ty.atom, Fixed, M),
  Both = constraint_set:merge_and_meet(PredefNormalize, AtomNormalize),
  case Both of
    [] -> [];
    _ ->

      IntervalNormalize = dnf_var_int:normalize(Ty#ty.interval, Fixed, M),
      Res1 = constraint_set:merge_and_meet(Both, IntervalNormalize),
      case Res1 of
        [] -> [];
        _ ->
          begin
                Res2 = multi_normalize_tuples(Ty#ty.tuple, Fixed, M),
                ResX = fun() -> constraint_set:merge_and_meet(Res1, Res2) end,
                ResLists = fun() -> dnf_var_ty_list:normalize(Ty#ty.list, Fixed, M) end,
                Res3 = constraint_set:meet(ResX, ResLists),
                case Res3 of
                  [] -> [];
                  _ ->
                    Res4 = multi_normalize_functions(Ty#ty.function, Fixed, M),
                    constraint_set:merge_and_meet(Res3, Res4)
                end
          end
      end
  end.

multi_normalize_tuples({Default, AllTuples}, Fixed, M) ->
  Others = ?F(
    maps:fold(fun(Size, V, Acc) ->
      constraint_set:meet(
        ?F(Acc),
        ?F(dnf_var_ty_tuple:normalize(Size, V, Fixed, M))
      )
              end, [[]], AllTuples)
  ),

  DF = ?F(dnf_var:normalize({default, maps:keys(AllTuples)}, Default, Fixed, M)),

  constraint_set:meet(
    DF,
    Others
  ).

multi_normalize_functions({Default, AllFunctions}, Fixed, M) ->
  Others = ?F(
    maps:fold(fun(Size, V, Acc) ->
      constraint_set:meet(
        ?F(Acc),
        ?F(dnf_var_ty_function:normalize(Size, V, Fixed, M))
      )
              end, [[]], AllFunctions)
  ),

  DF = ?F(dnf_var:normalize({default, maps:keys(AllFunctions)}, Default, Fixed, M)),

  constraint_set:meet(
    DF,
    Others
  ).


% SubstMap :: var => ty_rec
substitute_ty(#ty{
    predef = Predef,
    atom = Atoms,
    interval = Ints,
    list = Lists,
    tuple = {DefaultT, AllTuples},
    function = {DefaultF, AllFunctions}
    % bitstring = Bitstring, % TODO #BITSTRING
    % dynamic = Dynamic, % TODO #DYNAMIC
    % map = Map % TODO #MAP
  }, SubstituteMap, Memo) ->

  #ty{
    predef = ?TIME(vardef, dnf_var_predef:substitute(Predef, SubstituteMap, Memo, fun(TTy) -> pi(predef, TTy) end)),
    atom = ?TIME(atom, dnf_var_ty_atom:substitute(Atoms, SubstituteMap, Memo, fun(TTy) -> pi(atom, TTy) end)),
    interval = ?TIME(int, dnf_var_int:substitute(Ints, SubstituteMap, Memo, fun(TTy) -> pi(interval, TTy) end)),
    list = ?TIME(list, dnf_var_ty_list:substitute(Lists, SubstituteMap, Memo, fun(TTy) -> pi(list, TTy) end)),
    tuple = ?TIME(multi_tuple, multi_substitute(DefaultT, AllTuples, SubstituteMap, Memo)),
    function = ?TIME(multi_fun, multi_substitute_fun(DefaultF, AllFunctions, SubstituteMap, Memo))
  }.

tuple_keys(Type) ->
  Ty = type:load(Type),
  {_T, Map} = Ty#ty.tuple,
  maps:fold(fun(K,_,AccIn) -> [K | AccIn] end, [], Map).

function_keys(Type) ->
  Ty = type:load(Type),
  {_T, Map} = Ty#ty.function,
  maps:fold(fun(K,_,AccIn) -> [K | AccIn] end, [], Map).

multi_substitute(DefaultTuple, AllTuples, SubstituteMap, Memo) ->
  % substitute default tuple, get a new default tuple
  NewDefaultTuple = dnf_var_ty_tuple:substitute(DefaultTuple, SubstituteMap, Memo, fun(Ty) -> pi({tuple, default}, Ty) end),

  % the default tuple can be substituted to contain other explicit tuple lengths
  % example: {alpha, 0} with alpha := {1,1} ==> {0, 2 -> {1,1}}
  % projecting just the default tuple value 0 loses information
  % we need to get these explicit tuple lengths out of the substituted default tuple:
  % get all lengths after substitution,
  % and substitute the default tuple for each length,
  % filtering with the appropriate length projection function
  AllVars = dnf_var_ty_tuple:all_variables(DefaultTuple),
  % note: OtherTupleKeys not be included in the AllTuples keys, they are known
  % TODO erlang 26 map comprehensions
  Keys = maps:fold(fun(K,V,AccIn) -> case lists:member(K, AllVars) of true -> tuple_keys(V) -- maps:keys(AllTuples) ++ AccIn; _ -> AccIn end end, [], SubstituteMap),
  % Keys = [(tuple_keys(V) -- maps:keys(AllTuples)) || K := V <- SubstituteMap, lists:member(K, AllVars)],
  OtherTupleKeys = lists:usort(lists:flatten(Keys)),
  NewDefaultOtherTuples = maps:from_list([{Length, dnf_var_ty_tuple:substitute(DefaultTuple, SubstituteMap, Memo, fun(Ty) -> pi({tuple, Length}, Ty) end)} || Length <- OtherTupleKeys]),

  % all explicit keys are now all defined tuples and all newly explicit tuples after default substitution
  AllKeys = maps:keys(AllTuples) ++ maps:keys(NewDefaultOtherTuples),

  % {alpha, 0 => alpha} with alpha := {1} ==> {0, 1 => {1}}
  % for explicit tuples, collect all other lengths into a new map, yielding a list of maps
  % merge (union) these maps into NewOtherTuples
  NewOtherTuples = maps:from_list(lists:map(fun(Key) ->
    {Key, case maps:is_key(Key, AllTuples) of
            true ->
            dnf_var_ty_tuple:substitute(maps:get(Key, AllTuples), SubstituteMap, Memo, fun(Ty) -> pi({tuple, Key}, Ty) end);
            _ -> maps:get(Key, NewDefaultOtherTuples, NewDefaultTuple)
          end}
                                            end, AllKeys)),

  {NewDefaultTuple, NewOtherTuples}.

multi_substitute_fun(DefaultFunction, AllFunctions, SubstituteMap, Memo) ->
  % see multi_substitute for comments
  % TODO refactor abstract into one function for both tuples and funcions
  NewDefaultFunction = dnf_var_ty_function:substitute(DefaultFunction, SubstituteMap, Memo, fun(Ty) -> pi({function, default}, Ty) end),
  AllVars = dnf_var_ty_function:all_variables(DefaultFunction),
  % TODO erlang 26 map comprehensions
  Keys = maps:fold(fun(K,V,AccIn) -> case lists:member(K, AllVars) of true -> function_keys(V) -- maps:keys(AllFunctions) ++ AccIn; _ -> AccIn end end, [], SubstituteMap),
  % Keys = [function_keys(V) || K := V <- SubstituteMap, lists:member(K, AllVars)],
  OtherFunctionKeys = lists:usort(lists:flatten(Keys)),
  NewDefaultOtherFunctions = maps:from_list([{Length, dnf_var_ty_function:substitute(DefaultFunction, SubstituteMap, Memo, fun(Ty) -> pi({function, Length}, Ty) end)} || Length <- OtherFunctionKeys]),
  AllKeys = maps:keys(AllFunctions) ++ maps:keys(NewDefaultOtherFunctions),

  NewOtherFunctions = maps:from_list(lists:map(fun(Key) ->
    {Key, case maps:is_key(Key, AllFunctions) of
            true -> dnf_var_ty_function:substitute(maps:get(Key, AllFunctions), SubstituteMap, Memo, fun(Ty) -> pi({function, Key}, Ty) end);
            _ -> maps:get(Key, NewDefaultOtherFunctions, NewDefaultFunction)
          end}
                                            end, AllKeys)),

  {NewDefaultFunction, NewOtherFunctions}.

% TODO needed?
% has_ref(#ty{list = Lists, tuple = {Default, AllTuple}, function = {DefaultF, AllFunction}}, TyRef) ->
%   % TODO sanity remove
%   false = dnf_var_ty_tuple:has_ref(Default, TyRef), % should never happen
%   false = dnf_var_ty_function:has_ref(DefaultF, TyRef), % should never happen
%   dnf_var_ty_list:has_ref(Lists, TyRef)
%   orelse
%   maps:fold(fun(_K,T, All) -> All orelse dnf_var_ty_tuple:has_ref(T, TyRef) end, false, AllTuple)
%   orelse
%   maps:fold(fun(_K,F, All) -> All orelse dnf_var_ty_function:has_ref(F, TyRef) end, false, AllFunction).





-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

predef_any_test() ->
  T = ty_rec:predef(),
  io:format(user,"~s~n", [print(T)]),
  ok.

recursive_definition_test() ->
  test_utils:reset_ets(),
  Lists = type:new_type(),
  ListsBasic = type:new_type(),

  % nil
  Nil = ty_rec:atom(dnf_var_ty_atom:ty_atom(ty_atom:finite([nil]))),

  % (alpha, Lists)
  Alpha = ty_variable:new("alpha"),
  AlphaTy = ty_rec:variable(Alpha),
  Tuple = ty_rec:tuple(2, dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple([AlphaTy, Lists])))),
  Recursive = ty_rec:union(Nil, Tuple),

  type:define_type(Lists, type:load(Recursive)),

  SomeBasic = ty_rec:atom(dnf_var_ty_atom:ty_atom(ty_atom:finite([somebasic]))),
  SubstMap = #{Alpha => SomeBasic},
  Res = ty_rec:substitute(Lists, SubstMap),

  Tuple2 = ty_rec:tuple(2, dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple([SomeBasic, ListsBasic])))),
  Expected = ty_rec:union(Nil, Tuple2),
  % Expected is invalid after define_type!
  NewTy = type:define_type(ListsBasic, type:load(Expected)),

  true = ty_rec:is_equivalent(Res, NewTy),
  ok.

any_0tuple_test() ->
  AnyTuple = ty_rec:tuple(0, dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple([])))),
  AnyTuple2 = ty_rec:tuple(0, dnf_var_ty_tuple:any()),
  true = ty_rec:is_equivalent(AnyTuple, AnyTuple2),
  ok.

any_tuple_test() ->
  AnyTuple = ty_rec:tuple(1, dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple([ty_rec:any()])))),
  AnyTuple2 = ty_rec:tuple(1, dnf_var_ty_tuple:any()),
  true = ty_rec:is_equivalent(AnyTuple, AnyTuple2),
  ok.

nonempty_function_test() ->
  Function = ty_rec:function(1, dnf_var_ty_function:function(dnf_ty_function:function(ty_function:function([ty_rec:empty()], ty_rec:any())))),
  Function2 = ty_rec:function(1, dnf_var_ty_function:any()),
  true = ty_rec:is_subtype(Function, Function2),
  true = ty_rec:is_subtype(Function2, Function),
  ok.

-endif.
