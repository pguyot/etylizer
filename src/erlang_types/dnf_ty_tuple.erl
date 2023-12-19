-module(dnf_ty_tuple).

-define(debug, true).

-include_lib("sanity.hrl").

-compile({no_auto_import, [node/1]}).

-define(F(Z), fun() -> Z end).

-export([is_empty/1, normalize/6, substitute/4]).
-export([tuple/1, all_variables/1, transform/2]).
-export([has_ref/2, any/0, empty/0, equal/2, union/2, intersect/2, negate/1, diff/2]).

-define(T, 1).
-define(B, []).

any() -> ?T.
empty() -> ?B.

equal(?T, ?T) -> true;
equal(?T, _) -> false;
equal(_, ?T) -> false;
equal(A, A) -> true;
equal(A, B) -> false.

union(?T, _) -> ?T;
union(_, ?T) -> ?T;
union(?B, B) -> B;
union(B, ?B) -> B;
union(A, B) -> make_disjoint(dim(A++B), order(A ++ B)).

intersect(?T, B) -> B;
intersect(B, ?T) -> B;
intersect(?B, _) -> ?B;
intersect(_, ?B) -> ?B;
intersect(A, A) -> A;
intersect(A, B) -> 
  negate( union( negate(A), negate(B))).

negate(?T) -> ?B;
negate(?B) -> ?T;
negate(A) ->
  % Partitioning:
  %    (t,s) - ((t1,s1) | (t2,s2) | ... | (tn,sn))
  %     =
  %     (t & t1, s - s1) | ... | (t & tn, s - sn) | (t - (t1|...|tn), s)
  % Negation:
  % (Any, Any) - ((t1,s1) | ... |(tn,sn))
  % = (Any & t1, Any - s1) | ... | (Any & tn, Any - sn) | (Any - (t1|...|tn), Any)
  % = (t1, !s1) | ... | (tn, !sn) | (!(t1|...|tn), Any)
  ?TIME(negate_dnf, make_disjoint(dim(A), negate(dim(A), A))).
  

negate(1, Ts) ->
  [FirstTuple | Others] = [{ty_tuple, 1, [ty_rec:negate(C)]} || {ty_tuple, 1, [C]} <- Ts],
  Res = [lists:foldl(fun({ty_tuple, 1, [OtherTy]}, {ty_tuple, 1, [Ty]}) -> {ty_tuple, 1, [ty_rec:intersect(OtherTy, Ty)]} end, FirstTuple, Others)],
  1 = length(Res),
  Res;
negate(2, A) ->
  Res = lists:flatten(partition2({ty_rec:any(), ty_rec:any()}, A, [], ty_rec:empty())),
  (lists:filter(fun
    ({ty_tuple, 2, [_, {ty_ref, 1}]}) -> false;
    ({ty_tuple, 2, [{ty_ref, 1}, _]}) -> false;
    (_) -> true
  end, Res))
  ;
  % % [T1, ..., Tn]  =neg=>  [T1', ..., Tn', Tn+1']
  % Ordered = order(ResAll),
  % % io:format(user,"Negate: ~p~nRESULT~p~n", [A, Ordered]),
  % Ordered.
negate(Dim, A) ->
  error({todo, tuples, Dim}).


make_disjoint(_, []) -> [];
make_disjoint(_, [X]) -> [X];
make_disjoint(1, [Tup = {ty_tuple, 1, [_]} | Xs]) -> 
  [lists:foldl(fun({ty_tuple, 1, [E]}, {ty_tuple, 1, [T]}) -> {ty_tuple, 1, [ty_rec:union(E, T)]} end, Tup, Xs)];
make_disjoint(2, Xs) -> 
  SameLeft = merge_same_left(Xs, []),
  SameRight = merge_same_right(SameLeft, []),
  Disjoint = make_disj(SameRight, []),
  % check_all(Disjoint),
  Disjoint;
make_disjoint(_, Xs) -> error(todo).


make_disj([], Accu) -> Accu;
make_disj([X = {ty_tuple, 2, [L, R]} | Xs], Accu) -> 
  case is_disjoint_from(X, Xs) of
    true -> make_disj(Xs, [X | Accu]);
    {false, Rem = {ty_tuple, 2, [Left, Right]}} -> 
      Diff = ty_rec:intersect(L, Left),
      make_disj([{ty_tuple, 2, [ty_rec:diff(L, Diff), R]}, {ty_tuple, 2, [ty_rec:diff(Left, Diff),Right]}, {ty_tuple, 2, [Diff, ty_rec:union(R, Right)]}] ++ (Xs -- [Rem]), Accu)
  end.

check_all([]) -> ok;
check_all([X | Xs]) -> 
  true = is_disjoint_from(X, Xs),
  check_all(Xs).



is_disjoint_from(X, []) -> true;
is_disjoint_from(X = {ty_tuple, 2, [L, _]}, [Y = {ty_tuple, 2, [L2, _]} | Ts]) ->
  case ty_rec:is_empty(ty_rec:intersect(L, L2)) of
    true -> is_disjoint_from(X, Ts);
    _ -> {false, Y}
  end.
  


merge_same_left([], Accu) -> Accu;
merge_same_left([TT = {ty_tuple, 2, [Left, _]} | Xs], Accu) -> 
  Same = [T || T = {ty_tuple, 2, [L, _]} <- Xs, ty_rec:is_equivalent(Left, L)],
  SameLeftTuples = lists:foldl(fun({ty_tuple, 2, [_, E]}, {ty_tuple, 2, [_, T]}) -> {ty_tuple, 2, [Left, ty_rec:union(E, T)]} end, TT, Same),
  Others = Xs -- Same,
  merge_same_left(Others, [SameLeftTuples | Accu]).

merge_same_right([], Accu) -> Accu;
merge_same_right([TT = {ty_tuple, 2, [_, Right]} | Xs], Accu) -> 
  Same = [T || T = {ty_tuple, 2, [_, R]} <- Xs, ty_rec:is_equivalent(Right, R)],
  SameRightTuples = lists:foldl(fun({ty_tuple, 2, [E, _]}, {ty_tuple, 2, [T, _]}) -> {ty_tuple, 2, [ty_rec:union(E, T), Right]} end, TT, Same),
  Others = Xs -- Same,
  merge_same_right(Others, [SameRightTuples | Accu]).

partition2({T, S}, [], Accu, TUnion) ->
  OneDnf = [{ty_tuple, 2, [ty_rec:diff(T, TUnion), S]}],
  E = ty_rec:empty(),
  case OneDnf of
    {ty_tuple, 2, [E, _]} -> 
      Accu;
    {ty_tuple, 2, [_, E]} -> 
      Accu;
    _ -> 
      Accu ++ OneDnf
  end;
partition2({T, S}, [N | Negs], Accu, TUnion) ->
  {ty_tuple, 2, [T1, S1]} = N,
  Dnf = {ty_tuple, 2, [ty_rec:intersect(T, T1), ty_rec:diff(S, S1)]},
  E = ty_rec:empty(),
  case Dnf of
    {ty_tuple, 2, [E, _]} -> 
      partition2({T, S}, Negs, [Accu], ty_rec:union(T1, TUnion));
    {ty_tuple, 2, [_, E]} -> 
      partition2({T, S}, Negs, [Accu], ty_rec:union(T1, TUnion));
    _ -> 
      partition2({T, S}, Negs, [Dnf | Accu], ty_rec:union(T1, TUnion))
  end.

order(X) -> lists:usort(X).

dim([]) -> unknown;
dim([{ty_tuple, Dim, _} | _]) ->
  Dim.

diff(A, B) -> intersect(A, negate(B)).

all_variables(?T) -> [];
all_variables(Dnf) ->
  SS = fun(Tuple) -> ty_tuple:all_variables(Tuple) end,
  lists:usort(lists:flatten([SS(T) || T <- Dnf])).

has_ref(?T, _Ref) -> false;
has_ref(Dnf, Ref) ->
  lists:any(fun(E) -> ty_tuple:has_ref(E, Ref) end, Dnf).

substitute(?T, _Map, _Memo,_) -> ?T;
substitute(Dnf, Map, Memo, _) -> 
  [ty_tuple:substitute(T, Map, Memo) || T <- Dnf].

dnf(1, {ProcessCoclause, _CombineResults}) -> error(todo1);
dnf([], {ProcessCoclause, _CombineResults}) -> ProcessCoclause({[], [], 0});
dnf([C | Cs], {ProcessCoclause, CombineResults}) ->
  Ini = ProcessCoclause({[C], [], 1}),
  lists:foldl(
    fun(E,Acc) -> 
      CombineResults(?F(ProcessCoclause({[E], [], 1})), ?F(Acc)) 
  end, 
  Ini,
  Cs).
 
transform(1, Ops = #{any := Any, union := Union}) -> Any();
transform(Dnf, Ops = #{union := Union}) -> 
  SS = fun(Tuple) -> ty_tuple:transform(Tuple, Ops) end,
  Union([SS(C) || C <- Dnf])
.

tuple(TyTuple) -> [TyTuple].

is_empty(?T) -> false;
is_empty(?B) -> true;
is_empty(TyBDD) -> 
  Res = dnf(TyBDD, {fun is_empty_coclause/1, fun is_empty_union/2}),
  Res.

is_empty_union(F1, F2) ->
  F1() andalso F2().

is_empty_coclause({Pos, Neg, T}) ->
  case {Pos, Neg, bdd_bool:empty()} of
    {_, _, T} -> true;
    {[], [], _} -> false;
    {[], [TNeg | _], _} ->
      Dim = length(ty_tuple:components(TNeg)),
      PosAny = ty_tuple:any(Dim),
      BigS = ty_tuple:big_intersect([PosAny]),
      phi(ty_tuple:components(BigS), Neg);
    {Pos, Neg, _} ->
      BigS = ty_tuple:big_intersect(Pos),
      phi(ty_tuple:components(BigS), Neg)
  end.

phi(BigS, []) ->
  lists:foldl(fun(S, Res) -> Res orelse ty_rec:is_empty(S) end, false, BigS);
phi(BigS, [Ty | N]) ->
  Solve = fun({Index, {_PComponent, NComponent}}, Result) ->
    Result
      andalso
      begin
      % remove pi_Index(NegativeComponents) from pi_Index(PComponents) and continue searching
        DoDiff = fun({IIndex, PComp}) ->
          case IIndex of
            Index -> ty_rec:diff(PComp, NComponent);
            _ -> PComp
          end
                 end,
        NewBigS = lists:map(DoDiff, lists:zip(lists:seq(1, length(BigS)), BigS)),
        phi(NewBigS, N)
      end
          end,


  lists:foldl(fun(S, Res) -> Res orelse ty_rec:is_empty(S) end, false, BigS)
    orelse
      lists:foldl(Solve, true, lists:zip(lists:seq(1, length(ty_tuple:components(Ty))), lists:zip(BigS, ty_tuple:components(Ty)))).

normalize(Size, Ty, [], [], Fixed, M) ->
  dnf(Ty, {
    fun({Pos, Neg, T}) ->
      case bdd_bool:empty() of
        T -> [[]];
        _ ->
          BigS = ty_tuple:big_intersect(Pos),
          phi_norm(Size, ty_tuple:components(BigS), Neg, Fixed, M)
      end
    end,
    fun constraint_set:meet/2
  });
normalize(Size, DnfTy, PVar, NVar, Fixed, M) ->
  Ty = ty_rec:tuple(Size, dnf_var_ty_tuple:tuple(DnfTy)),
  % ntlv rule
  ty_variable:normalize(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:tuple(Size, dnf_var_ty_tuple:var(Var)) end, M).

phi_norm(_Size, BigS, [], Fixed, M) ->
  lists:foldl(fun(S, Res) -> constraint_set:join(?F(Res), ?F(ty_rec:normalize(S, Fixed, M))) end, [], BigS);
phi_norm(Size, BigS, [Ty | N], Fixed, M) ->
  Solve = fun({Index, {_PComponent, NComponent}}, Result) ->
    constraint_set:meet(
      ?F(Result),
      ?F(begin
      % remove pi_Index(NegativeComponents) from pi_Index(PComponents) and continue searching
        DoDiff = fun({IIndex, PComp}) ->
          case IIndex of
            Index ->
              ty_rec:diff(PComp, NComponent);
            _ -> PComp
          end
                 end,
        NewBigS = lists:map(DoDiff, lists:zip(lists:seq(1, length(BigS)), BigS)),
        phi_norm(Size, NewBigS, N, Fixed, M)
      end)
    )
          end,

  constraint_set:join(
    ?F(lists:foldl(fun(S, Res) -> constraint_set:join(?F(Res), ?F(ty_rec:normalize(S, Fixed, M))) end, [], BigS)),
    ?F(lists:foldl(Solve, [[]], lists:zip(lists:seq(1, length(ty_tuple:components(Ty))), lists:zip(BigS, ty_tuple:components(Ty)))))
  ).

