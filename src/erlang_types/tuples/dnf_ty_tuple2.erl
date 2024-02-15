-module(dnf_ty_tuple).

-define(debug, true).
-include_lib("sanity.hrl").

-compile({no_auto_import, [node/1]}).

-define(F(Z), fun() -> Z end).

-export([is_empty/1, normalize/6, substitute/4]).
-export([tuple/1, all_variables/1, transform/2]).
-export([has_ref/2, any/0, empty/0, equal/2, union/2, intersect/2, negate/1, diff/2]).

-define(T, top_tuple).
-define(B, bottom_tuple).

any() -> ?T.
empty() -> ?B.

% syntactic equality
equal(?T, ?T) -> true;
equal(?T, _) -> false;
equal(_, ?T) -> false;
% top_tuple of dimension n is not equal to top_tuple of dimension m, n !=m.
% caller should make sure that equal is only called on the same tuple kind
equal(A, A) -> true;
equal(_, _) -> false.

union(?T, _) -> ?T;
union(_, ?T) -> ?T;
union(?B, B) -> B;
union(B, ?B) -> B;
union(B, B) -> B;
union(A, B) -> 
  case dim([A, B]) of
    0 -> error(todo_dim_0);
    1 -> error(todo_dim_1);
    2 -> 
      % can't just concatenate A++B, then the tuples are not disjoint anymore in the first component!
      make_disjoint(dim(A++B), order(dim(A++B), A ++ B));
    _ -> 
        error(todo_dim_tuple_n)
      %make_disjoint(dim(A++B), order(dim(A++B), A ++ B))
  end.
   

intersect(?T, B) -> B;
intersect(B, ?T) -> B;
intersect(?B, _) -> ?B;
intersect(_, ?B) -> ?B;
intersect(A, A) -> A;
intersect(A, B) -> 
  negate(union(negate(A), negate(B))).

negate(?T) -> ?B;
negate(?B) -> ?T;
negate(A) ->
  case dim([A]) of
    0 -> error(todo_dim_0);
    1 -> error(todo_dim_1);
    2 -> 
      % Partitioning:
      %    (t,s) - ((t1,s1) | (t2,s2) | ... | (tn,sn))
      %     =
      %     (t & t1, s - s1) | ... | (t & tn, s - sn) | (t - (t1|...|tn), s)
      % Negation:
      % (Any, Any) - ((t1,s1) | ... |(tn,sn))
      % = (Any & t1, Any - s1) | ... | (Any & tn, Any - sn) | (Any - (t1|...|tn), Any)
      % = (t1, !s1) | ... | (tn, !sn) | (!(t1|...|tn), Any)
      ?TIME(negate_2_tuple, make_disjoint(dim(A), negate(dim(A), A)));
    _ -> 
      error(todo_dim_tuple_n)
  end.
  

negate(1, Ts) ->
  [FirstTuple | Others] = [{ty_tuple, 1, [ty_rec:negate(C)]} || {ty_tuple, 1, [C]} <- Ts],
  Res = [lists:foldl(fun({ty_tuple, 1, [OtherTy]}, {ty_tuple, 1, [Ty]}) -> {ty_tuple, 1, [ty_rec:intersect(OtherTy, Ty)]} end, FirstTuple, Others)],
  1 = length(Res),
  Res;
negate(2, A) ->
  R = normal_cduce([_SingleCoClause = {_P = [{ty_rec:any(), ty_rec:any()}], _N = [{S, T} || {ty_tuple, 2, [S, T]} <- A]}]),
  [{ty_tuple, 2, [T1, T2]} || {T1, T2} <- R];
negate(Dim, A) ->
  error({todo, tuples, Dim}).


make_disjoint(_, []) -> [];
make_disjoint(_, [X]) -> [X];
make_disjoint(1, [Tup = {ty_tuple, 1, [_]} | Xs]) -> 
  [lists:foldl(fun({ty_tuple, 1, [E]}, {ty_tuple, 1, [T]}) -> {ty_tuple, 1, [ty_rec:union(E, T)]} end, Tup, Xs)];
make_disjoint(2, Res) -> Res;
make_disjoint(_, Xs) -> error(todo).


order(1, X) -> lists:usort(X);
order(2, X) -> 
  Dnf = [{_Pi = [{S, T}], _Ni = []} || {ty_tuple, 2, [S, T]} <- X],
  Res = normal_cduce(Dnf),
  [{ty_tuple, 2, [T1, T2]} || {T1, T2} <- Res].

dim([{ty_tuple, Dim, _} | _]) -> Dim;
dim({ty_tuple, Dim, _}) -> Dim;
dim(_) -> error(unknown_tuple_dimension).

diff(A, B) -> 
  intersect(A, negate(B)).

all_variables(?T) -> [];
all_variables(?B) -> [];
all_variables(Ty) ->
  case dim(Ty) of
    0 -> error(todo_dim_0);
    1 -> error(todo_dim_1);
    2 -> 
        SS = fun(Tuple) -> ty_tuple:all_variables(Tuple) end,
        lists:usort(lists:flatten([SS(T) || T <- Ty]));
    _ -> error(todo_dim_tuple_n)
  end.

has_ref(?T, _Ref) -> false;
has_ref(?B, _Ref) -> false;
has_ref(Ty, Ref) ->
  case dim(Ty) of
    0 -> error(todo_dim_0);
    1 -> error(todo_dim_1);
    2 -> 
        lists:any(fun(E) -> ty_tuple:has_ref(E, Ref) end, Ty);
    _ -> error(todo_dim_tuple_n)
  end.

substitute(?T, _Map, _Memo,_) -> ?T;
substitute(?B, _Map, _Memo,_) -> ?B;
substitute(Ty, Map, Memo, _) -> 
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







% =================
% CDuce code border


normal_cduce(X) ->
  cleanup(lists:foldl(fun line/2, [], X)).

cleanup(L) ->
  Aux = fun A({T1, T2}, Accu) ->
    case Accu of
      [] -> [{T1, T2}];
      [{S1, S2} | Rem] -> 
        case ty_rec:is_equivalent(T2, S2) of
          true -> [{ty_rec:union(S1, T1), S2}| Rem];
          _ -> [{S1, S2} | A({T1, T2}, Rem)]
        end
    end
  end,
  lists:foldl(Aux, [], L).

bigcap(T1, T2, []) -> {T1, T2};
bigcap(T1, T2, [{S1, S2} | Rem]) -> 
  bigcap(ty_rec:intersect(T1, S1), ty_rec:intersect(T2, S2), Rem).

line({P, N}, Accu) ->
  {D1, D2} = bigcap(ty_rec:any(), ty_rec:any(), P),
  case not (ty_rec:is_empty(D1) orelse ty_rec:is_empty(D2)) of
    true -> 
      Resid = make_ref(), put(Resid, ty_rec:empty()),
      F = fun({T1, T2}, FAccu) -> 
        I = ty_rec:intersect(D1, T1),
        case not ty_rec:is_empty(I) of
          true ->
            put(Resid, ty_rec:union(get(Resid), T1)),
            T2new = ty_rec:diff(D2, T2),
            case not ty_rec:is_empty(T2new) of
              true -> add([], I, T2new, FAccu);
              _ -> FAccu 
            end;
          _ -> 
            FAccu
        end
      end,

      NewAccu = lists:foldl(F, Accu, normal(N)),
      NewD1 = ty_rec:diff(D1, get(Resid)),
      case not ty_rec:is_empty(NewD1) of
        true -> add([], NewD1, D2, NewAccu);
        _ -> NewAccu
      end;
    _ -> Accu
  end.


normal(X) ->
  lists:foldl(fun({T1, T2}, Accu) -> 
    add([], T1, T2, Accu) 
  end, [], X).

add(Root, T1, T2, []) ->
  [{T1, T2} | Root];
add(Root, T1, T2, [{S1, S2} | Rem]) ->
  I = ty_rec:intersect(T1, S1),
  case ty_rec:is_empty(I) of
    true -> add([{S1, S2} | Root], T1, T2, Rem);
    _ ->
      NewRoot = [{I, ty_rec:union(T2, S2)} | Root],
      K = ty_rec:diff(S1, T1),
      NewRoot2 = case not ty_rec:is_empty(K) of
        true -> [{K, S2} | NewRoot];
        _ -> NewRoot
      end,
      J = ty_rec:diff(T1, S1),
      case not ty_rec:is_empty(J) of
        true -> add(NewRoot2, J, T2, Rem);
        _ -> 
          %lists:reverse(NewRoot2) ++ Rem
          lists:reverse(NewRoot2) ++ Rem
      end
  end.


-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

% conversion and projection for dnf_ty_tuple
% pi(Ty, Rank) ->
%   T = test_utils:mini_to_erlang_ty(Ty),
%   % assume no variables
%   [] = ty_rec:all_variables(T),
%   {terminal, DnfTyTuple} = ty_rec:pi({tuple, Rank}, TyRef),
%   DnfTyTuple.


empty_any_2_test() ->
  Ty = fun(T) -> test_utils:mini_to_erlang_ty(T) end,
  test_utils:reset_ets(),
  N = fun(T) -> ty_rec:negate(T) end,
  I = fun(S,T) -> ty_rec:intersect(S,T) end,

  E0 = Ty(empty),
  Any = Ty(any),
  E1 = Ty({empty, empty}),
  At = Ty({atom}),
  A = Ty(a),
  NA = Ty({'!', a}),
  B = Ty({b}),

  true = ty_rec:is_subtype(E1, E1),
  true = ty_rec:is_subtype(E1, Any),
  true = ty_rec:is_subtype(Any, Any),
  true = ty_rec:is_empty(E1),
  false = ty_rec:is_empty(Any),
  true = ty_rec:is_subtype(Any, N(E1)),
  true = ty_rec:is_empty(N(N(E1))),
  true = ty_rec:is_empty(I(E1, E1)),
  true = ty_rec:is_empty(I(E1, A)),

  % part of de morgan
  % Z1 = Ty(
  %   {
  %   {{{'!', a}, any}, '|', {a, {'!', a}}},
  %   '&',
  %   {a,a}
  %   }
  % ),
  % true = ty_rec:is_empty(Z1),

  % de morgan
  % ZZ = Ty({'!', {a, a}}),
  % NZ = Ty({'!', {a, a}}),
  % true = ty_rec:is_subtype(ZZ, NZ),
  % true = ty_rec:is_subtype(NZ, ZZ),

  % S = Ty({{a, '|', b}, c}),
  % T = Ty({{a, c}, '|', {b, c}}),
  % true = ty_rec:is_subtype(S, T),


  % S = p(u(b(alpha), b(beta)), b(gamma)),
  % T = u(p(b(alpha), b(gamma)), p(b(beta), b(gamma))),


  ok.

-endif.
