-module(ty_variable).

-define(debug, true).

-include_lib("../log.hrl").
-include_lib("sanity.hrl").


% Top-level type container
-define(TY, ty_rec).

-export_type([type/0]).
-opaque type() :: var().

-export([print_ty/1, equal/2, compare/2, substitute/4, all_variables/2, name/1]).

-export([new/1, normalize/6, transform/2]).

% Variables are totally ordered.
% We define the total order via a unique ID.
% The ID is assigned at variable creation time.
% The last assigned ID is tracked in a global state.
% 
% Variables are either polymorphic or monomorphic.
% This is not tracked inside this data structure;
% they are tracked in a given 'delta' set, 
% e.g. when calling tally.

% ======
% GLOBAL STATE
% ======

% The state keeps track of:
% * the last index used by a variable
-record(s, {variable_id = 0}).
-type s() :: #s{}.

-spec get_state() -> s().
get_state() ->
  State = get(?MODULE),
  case State of
    undefined -> empty_state();
    _ -> State
  end.

-spec update_state(s()) -> ok.
update_state(S) ->
  put(?MODULE, S),
  ok.

-spec empty_state() -> s().
empty_state() ->
  #s{variable_id = 0}.

-spec new_variable_id() -> integer().
new_variable_id() -> 
  (S = #s{variable_id = UsedId}) = get_state(),
  ok = update_state(S#s{variable_id = UsedId + 1}),
  UsedId + 1.

% ======
% DATA STRUCTURE, CONSTRUCTORS
% ======
  
-record(var, {id, name}).
-type var() :: #var{id :: integer(), name :: string()}.

-spec name(var()) -> string().
name(#var{name = Name}) -> Name.

-spec new(string()) -> var().
new(Name) ->
  % TODO sanity check: creating a variable with an already used name -> warning
  NewId = new_variable_id(),
  ?LOG_TRACE("[ty_variable:new/1] ~p (~p)", Name, NewId),
  #var{id = NewId, name = Name}.

-spec equal(var(), var()) -> boolean().
equal(Var1, Var2) -> compare(Var1, Var2) =:= 0.

-spec compare(var(), var()) -> -1 | 0 | 1.
compare(#var{id = Id1}, #var{id = Id2}) when Id1 < Id2 -> -1;
compare(#var{id = Id1}, #var{id = Id2}) when Id1 > Id2 -> +1;
compare(_, _) -> 0.

% total order function
-spec leq(var(), var()) -> boolean().
leq(#var{id = Id1}, #var{id = Id2}) -> Id1 =< Id2.

% ======
% PRETTY PRINTING
% ======
 
-spec print_ty(var()) -> prettypr:doc().
print_ty(#var{id = _Id, name = Name}) -> 
  epretty:text(Name). % TODO variable printing, what to do with ID?

% ======
% SET-THEORETIC API
% ======

single(Pol, VPos, VNeg, Ty, VarToTy) ->
  AccP = lists:foldl(fun(Var, TTy) -> ?TY:intersect(TTy, VarToTy(Var)) end, Ty, VPos),
  AccN = lists:foldl(fun(Var, TTy) -> ?TY:union(TTy, VarToTy(Var)) end, ?TY:empty(), VNeg),
  S = ?TY:diff(AccP, AccN),
  case Pol of
    true -> ?TY:negate(S);
    _ -> S
  end.

% (NTLV rule)
normalize(Ty, PVar, NVar, Fixed, VarToTy, Mx) ->
  SmallestVar = smallest(PVar, NVar, Fixed),
  case SmallestVar of
    {{pos, Var}, _Others} ->
      Singled = single(true, PVar -- [Var], NVar, Ty, VarToTy ),
      [[{Var, ?TY:empty(), Singled}]];
    {{neg, Var}, _Others} ->
      Singled = single(false, PVar, NVar -- [Var], Ty, VarToTy),
      [[{Var, Singled, ?TY:any()}]];
    {{{delta, _}, _}, _} ->
      % part 1 paper Lemma C.3 and C.11 all fixed variables can be eliminated
      ?TY:normalize(Ty, Fixed, Mx)
  end.

substitute(MkTy, Var, Map, _Memo) ->
  X = maps:get(Var, Map, ?TY:variable(Var)),
  MkTy(X).

all_variables(Var, _) -> [Var].
transform(Ty, #{var := ToVar}) -> ToVar(Ty).


% ======
% PRIVATE
% ======
  
% assumption: PVars U NVars is not empty
-spec smallest(list(var()), list(var()), list(var())) -> {any(), any()}. % TODO return spec
smallest(PositiveVariables, NegativeVariables, FixedVariables) ->
  ?SANITY(pvars_nvars_not_empty, true = (length(PositiveVariables) + length(NegativeVariables)) > 0),

  % fixed variables are higher order than all non-fixed ones, will be picked last
  PositiveVariablesTagged = [{pos, V} || V <- PositiveVariables, not sets:is_element(V, FixedVariables)],
  NegativeVariablesTagged = [{neg, V} || V <- NegativeVariables, not sets:is_element(V, FixedVariables)],

  RestTagged =
    [{{delta, neg}, V} || V <- NegativeVariables, sets:is_element(V, FixedVariables)] ++
    [{{delta, pos}, V} || V <- PositiveVariables, sets:is_element(V, FixedVariables)],

  Sort = fun({_, V}, {_, V2}) -> leq(V, V2) end,
  [X | Z] = lists:sort(Sort, PositiveVariablesTagged++NegativeVariablesTagged) ++ lists:sort(Sort, RestTagged),

  {X, Z}.


-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

usage_test() ->
  % create a fresh variable with a descriptor "A"
  VarA = new("A"),
  "A" = name(VarA),
  ok.

print_test() ->
  % print currently only prints the name
  VarA = new("A"),
  "A" = epretty:render(print_ty(VarA)),
  ok.

strictly_increasing_id_test() ->
  #var{id = IdA} = new("A"),
  #var{id = IdB} = new("B"),
  #var{id = IdC} = new("C"),
  true = (IdA < IdB),
  true = (IdB < IdC),
  ok.

same_name_different_id_test() ->
  VarA = new("a"),
  VarB = new("a"),
  -1 = compare(VarA, VarB),
  ok.

-endif.

