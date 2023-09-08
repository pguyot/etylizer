-module(ty_rec).
-vsn({2,0,0}).

-define(F(Z), fun() -> Z end).

-behavior(type).
-export([empty/0, any/0]).
-export([union/2, negate/1, intersect/2, diff/2, is_any/1]).
-export([is_empty/1, eval/1]).

% additional type constructors
-export([function/1, variable/1, atom/1, interval/1, tuple/2]).
% type constructors with type refs
-export([function/2]).
% top type constructors
-export([function/0, atom/0, interval/0, tuple/0, ty_of/4]).

-export([is_equivalent/2, is_subtype/2, normalize/3]).

-export([substitute/2, substitute/3, pi/2, all_variables/1]).

-export([transform/2]).

-record(ty, {atom, interval, tuple, function}).

-type ty_ref() :: {ty_ref, integer()}.
-type interval() :: term().
-type ty_tuple() :: term().
-type ty_function() :: term().
-type ty_variable() :: term().
-type ty_atom() :: term().


% ======
% top-level API
% ======

ty_of(Atom, Int, Tuple, Function) ->
  #ty{atom = Atom, interval = Int, tuple = Tuple, function = Function}.

is_subtype(TyRef1, TyRef2) ->
  NewTy = intersect(TyRef1, ty_rec:negate(TyRef2)),

  is_empty(NewTy).

is_equivalent(TyRef1, TyRef2) ->
  is_subtype(TyRef1, TyRef2) andalso is_subtype(TyRef2, TyRef1).

transform(TyRef, Ops =
  #{
    any_tuple := Tuples,
    any_fun := Functions,
    any_int := Intervals,
    any_atom := Atoms,
    union := Union,
    intersect := Intersect
  }) ->
  Ty = ty_ref:load(TyRef),
  #ty{atom = A, interval = I, tuple = {DT, T}, function = F} = Ty,

  NA = Intersect([Atoms(), dnf_var_ty_atom:transform(A, Ops)]),
  NI = Intersect([Intervals(), dnf_var_int:transform(I, Ops)]),
  NT = Intersect([Tuples(), multi_transform(DT, T, Ops)]),
  NF = Intersect([Functions(), dnf_var_ty_function:transform(F, Ops)]),


  Union([NA, NI, NT, NF]).

multi_transform(DefaultT, T, Ops = #{negate := Negate, union := Union, intersect := Intersect}) ->
  X1 = dnf_var_ty_tuple:transform(DefaultT, Ops),
  Xs = lists:map(fun({_Size, Tuple}) -> dnf_var_ty_tuple:transform(Tuple, Ops) end, maps:to_list(T)),

  Union([Intersect([X1, Negate(Union(Xs))]), Union(Xs)]).


% ======
% Type constructors
% ======

%%rep_map_any()  -> {dnf_ty_variable:any(), #{}}.
%%rep_map_none() -> {dnf_ty_variable:empty(), #{}}.

-spec empty() -> ty_ref().
empty() ->
  ty_ref:store(#ty{
    atom = dnf_var_ty_atom:empty(),
    interval = dnf_var_int:empty(),
    tuple = {dnf_var_ty_tuple:empty(), #{}},
    function = dnf_var_ty_function:empty()
  }).

-spec any() -> ty_ref().
any() ->
  ty_ref:any().

-spec variable(ty_variable()) -> ty_ref().
variable(Var) ->
  Any = ty_ref:load(any()),

  ty_ref:store(Any#ty{
    atom = dnf_var_ty_atom:intersect(Any#ty.atom, dnf_var_ty_atom:ty_var(Var)),
    interval = dnf_var_int:intersect(Any#ty.interval, dnf_var_int:var(Var)),
    tuple = {dnf_var_ty_tuple:var(Var), #{}},
    function = dnf_var_ty_function:intersect(Any#ty.function, dnf_var_ty_function:var(Var))
  }).

-spec atom(ty_atom()) -> ty_ref().
atom(Atom) ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ atom = Atom }).

-spec atom() -> ty_ref().
atom() -> atom(dnf_var_ty_atom:any()).

-spec interval(interval()) -> ty_ref().
interval(Interval) ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ interval = Interval }).

-spec interval() -> ty_ref().
interval() -> interval(dnf_var_int:any()).

%%-spec tuple(ty_tuple()) -> ty_ref().
tuple({default, Sizes}, Tuple) ->
  NotCaptured = maps:from_list(lists:map(fun(Size) -> {Size, dnf_var_ty_tuple:empty()} end, Sizes)),
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ tuple = {Tuple, NotCaptured}});
tuple(ComponentSize, Tuple) ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ tuple = {dnf_var_ty_tuple:empty(), #{ComponentSize => Tuple}} }).

-spec tuple() -> ty_ref().
tuple() ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ tuple = {dnf_var_ty_tuple:any(), #{}} }).

-spec function(ty_ref(), ty_ref()) -> ty_ref().
function(A, B) ->
  Empty = ty_ref:load(empty()),
  Fun = dnf_var_ty_function:function(dnf_ty_function:function(ty_function:function(A, B))),
  ty_ref:store(Empty#ty{ function = Fun }).

-spec function(ty_function()) -> ty_ref().
function(Fun) ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ function = Fun }).

-spec function() -> ty_ref().
function() ->
  function(dnf_var_ty_function:any()).

% ======
% Boolean operations
% ======

-spec intersect(ty_ref(), ty_ref()) -> ty_ref().
intersect(TyRef1, TyRef2) ->
  #ty{atom = A1, interval = I1, tuple = T1, function = F1} = ty_ref:load(TyRef1),
  #ty{atom = A2, interval = I2, tuple = T2, function = F2} = ty_ref:load(TyRef2),
  ty_ref:store(#ty{
    atom = dnf_var_ty_atom:intersect(A1, A2),
    interval = dnf_var_int:intersect(I1, I2),
    tuple = multi_intersect(T1, T2),
    function = dnf_var_ty_function:intersect(F1, F2)
  }).

-spec negate(ty_ref()) -> ty_ref().
negate(TyRef1) ->
  Ty = #ty{atom = A1, interval = I1, tuple = {DT, T}, function = F1} = ty_ref:load(TyRef1),
  ty_ref:store(#ty{
    atom = dnf_var_ty_atom:negate(A1),
    interval = dnf_var_int:negate(I1),
    tuple = {dnf_var_ty_tuple:negate(DT), maps:map(fun(_K,V) -> dnf_var_ty_tuple:negate(V) end, T)},
    function = dnf_var_ty_function:negate(F1)
  }).

-spec diff(ty_ref(), ty_ref()) -> ty_ref().
diff(A, B) -> intersect(A, negate(B)).

-spec union(ty_ref(), ty_ref()) -> ty_ref().
union(A, B) -> negate(intersect(negate(A), negate(B))).

multi_intersect({DefaultT1, T1}, {DefaultT2, T2}) ->
  % get all keys
  AllKeys = maps:keys(T1) ++ maps:keys(T2),
  IntersectKey = fun(Key) ->
    dnf_var_ty_tuple:intersect(
      maps:get(Key, T1, DefaultT1),
      maps:get(Key, T2, DefaultT2)
    )
                 end,
  {dnf_var_ty_tuple:intersect(DefaultT1, DefaultT2), maps:from_list([{Key, IntersectKey(Key)} || Key <- AllKeys])}.


is_empty(TyRef) ->
  % first try op-cache
  case ty_ref:is_empty_cached(TyRef) of
    R when R == true; R == false -> R;
    miss ->
      ty_ref:store_is_empty_cached(TyRef, is_empty_miss(TyRef))
  end.

is_empty_miss(TyRef) ->
  Ty = ty_ref:load(TyRef),
  dnf_var_ty_atom:is_empty(Ty#ty.atom)
    andalso dnf_var_int:is_empty(Ty#ty.interval)
    andalso (
      begin
        case ty_ref:is_empty_memoized(TyRef) of
          true -> true;
          miss ->
            % memoize
            ok = ty_ref:memoize(TyRef),
            multi_empty_tuples(Ty#ty.tuple)
              andalso dnf_var_ty_function:is_empty(Ty#ty.function)
        end
      end
  ).

multi_empty_tuples({Default, AllTuples}) ->
  dnf_var_ty_tuple:is_empty(default, Default)
    andalso
  maps:fold(fun(Size, V, Acc) -> Acc andalso dnf_var_ty_tuple:is_empty(Size, V) end, true, AllTuples).

% TODO implement witness
eval(_) ->
  erlang:error(eval_witness_not_implemented).


is_any(_Arg0) ->
  erlang:error(any_not_implemented). % TODO needed?

normalize(TyRef, Fixed, M) ->
  Ty = ty_ref:load(TyRef),
  AtomNormalize = dnf_var_ty_atom:normalize(Ty#ty.atom, Fixed, M),
  case AtomNormalize of
    [] -> [];
    _ ->
      IntervalNormalize = dnf_var_int:normalize(Ty#ty.interval, Fixed, M),
      Res1 = constraint_set:merge_and_meet(AtomNormalize, IntervalNormalize),
      case Res1 of
        [] -> [];
        _ ->
          begin
                Res2 = multi_normalize_tuples(Ty#ty.tuple, Fixed, M),
                Res3 = constraint_set:merge_and_meet(Res1, Res2),
                case Res3 of
                  [] -> [];
                  _ ->
                    Res4 = dnf_var_ty_function:normalize(Ty#ty.function, Fixed, M),
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

  DF = ?F(dnf_var_ty_tuple:normalize({default, maps:keys(AllTuples)}, Default, Fixed, M)),

  constraint_set:meet(
    DF,
    Others
  ).

substitute(TyRef, SubstituteMap) ->
  substitute(TyRef, SubstituteMap, #{}).

substitute(TyRef, SubstituteMap, OldMemo) ->
  case maps:get(TyRef, OldMemo, undefined) of
    undefined ->
      Ty = #ty{
        atom = Atoms,
        interval = Ints,
        tuple = {DefaultT, AllTuples},
        function = Functions
      } = ty_ref:load(TyRef),

      io:format(user, "Substitute ~p to ~p~n", [Ty, SubstituteMap]),

      case has_ref(Ty, TyRef) of
        true ->
          RecursiveNewRef = ty_ref:new_ty_ref(),
          Memo = OldMemo#{TyRef => RecursiveNewRef},
          NewTy = #ty{
            atom = dnf_var_ty_atom:substitute(Atoms, SubstituteMap),
            interval = dnf_var_int:substitute(Ints, SubstituteMap),
            tuple = multi_substitute(DefaultT, AllTuples, SubstituteMap, Memo),
            function = dnf_var_ty_function:substitute(Functions, SubstituteMap, Memo)
          },
          ty_ref:define_ty_ref(RecursiveNewRef, NewTy);
        false ->
          NewTy = #ty{
            atom = dnf_var_ty_atom:substitute(Atoms, SubstituteMap),
            interval = dnf_var_int:substitute(Ints, SubstituteMap),
            tuple = multi_substitute(DefaultT, AllTuples, SubstituteMap, OldMemo),
            function = dnf_var_ty_function:substitute(Functions, SubstituteMap, OldMemo)
          },
          ty_ref:store(NewTy)
      end;

    ToReplace -> ToReplace
  end.

multi_substitute(DefaultTuple, AllTuples, SubstituteMap, Memo) ->
  {NewDefaultTuple, NewDefaultOtherTuples} = dnf_var_ty_tuple:substitute(default, DefaultTuple, SubstituteMap, Memo),

  AllKeys = maps:keys(AllTuples) ++ maps:keys(NewDefaultOtherTuples),
  % [] = [X || X <- AllKeys, X == default],

  NewOtherTuples = maps:from_list(lists:map(fun(Key) ->
    {Key, case maps:is_key(Key, AllTuples) of
            true ->
              {X, M} = dnf_var_ty_tuple:substitute(Key, maps:get(Key, AllTuples), SubstituteMap, Memo),
              maps:get(Key, M)
            ;
            _ -> maps:get(Key, NewDefaultOtherTuples, NewDefaultTuple)
          end}
                                            end, AllKeys)),

  {NewDefaultTuple, NewOtherTuples}.

has_ref(#ty{tuple = {Default, AllTuple}, function = Function}, TyRef) ->
  % TODO sanity remove
  false = dnf_var_ty_tuple:has_ref(Default, TyRef), % should never happen
  maps:fold(fun(_K,T, All) -> All orelse dnf_var_ty_tuple:has_ref(T, TyRef) end, false, AllTuple)
   orelse dnf_var_ty_function:has_ref(Function, TyRef).

pi(atom, TyRef) ->
  Ty = ty_ref:load(TyRef),
  Ty#ty.atom;
pi(interval, TyRef) ->
  Ty = ty_ref:load(TyRef),
  Ty#ty.interval;
pi(tuple, TyRef) ->
  Ty = ty_ref:load(TyRef),
  Ty#ty.tuple;
pi(function, TyRef) ->
  Ty = ty_ref:load(TyRef),
  Ty#ty.function.

all_variables(TyRef) ->
  #ty{
    atom = Atoms,
    interval = Ints,
    tuple = Tuples,
    function = Functions
  } = ty_ref:load(TyRef),


  lists:usort(dnf_var_ty_atom:all_variables(Atoms)
  ++ dnf_var_int:all_variables(Ints)
    ++ dnf_var_ty_tuple:all_variables(Tuples)
    ++ dnf_var_ty_function:all_variables(Functions)).

%%-ifdef(TEST).
%%-include_lib("eunit/include/eunit.hrl").
%%
%%usage_test() ->
%%  Lists = ty_ref:new_ty_ref(),
%%  ListsBasic = ty_ref:new_ty_ref(),
%%
%%  % nil
%%  Nil = ty_rec:atom(dnf_var_ty_atom:ty_atom(ty_atom:finite([nil]))),
%%
%%  % (alpha, Lists)
%%  Alpha = ty_variable:new("alpha"),
%%  AlphaTy = ty_rec:variable(Alpha),
%%  Tuple = ty_rec:tuple(dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple([AlphaTy, Lists])))),
%%  Recursive = ty_rec:union(Nil, Tuple),
%%
%%  ty_ref:define_ty_ref(Lists, ty_ref:load(Recursive)),
%%
%%  SomeBasic = ty_rec:atom(dnf_var_ty_atom:ty_atom(ty_atom:finite([somebasic]))),
%%  SubstMap = #{Alpha => SomeBasic},
%%  Res = ty_rec:substitute(Lists, SubstMap),
%%
%%  Tuple2 = ty_rec:tuple(dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple([SomeBasic, ListsBasic])))),
%%  Expected = ty_rec:union(Nil, Tuple2),
%%  ty_ref:define_ty_ref(ListsBasic, ty_ref:load(Expected)),
%%
%%  true = ty_rec:is_equivalent(Res, Expected),
%%
%%  ok.
%%
%%-endif.
