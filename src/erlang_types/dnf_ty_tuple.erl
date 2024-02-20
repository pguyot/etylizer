-module(dnf_ty_tuple).

-define(ELEMENT, b_product).
-define(TERMINAL, bdd_bool).
-define(F(Z), fun() -> Z end).

-export([is_empty/1, normalize/6, substitute/4, apply_to_node/3]).
-export([tuple/1, all_variables/1, transform/3, transform/2]).

-include("bdd_node.hrl").

tuple(TyTuple) -> node(TyTuple).

is_empty(TyBDD) ->
  dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).

  
is_empty_coclause(Pos, Neg, T) ->
  case {Pos, Neg, ?TERMINAL:empty()} of
    {_, _, T} -> true;
    {[], [], _} -> false;
    {[], [_ | _], _} ->
      is_empty_coclause([b_product:any()], Neg, T);
    {_, _, _} ->
      BigS = ?ELEMENT:big_intersect(Pos),
      phi(?ELEMENT:pi1(BigS), ?ELEMENT:pi2(BigS), Neg)
  end.

phi(S1, S2, []) ->
  ty_rec:is_empty(S1)
    orelse
    ty_rec:is_empty(S2);
phi(S1, S2, [Ty | N]) ->
  ty_rec:is_empty(S1)
    orelse ty_rec:is_empty(S2)
    orelse (
      begin
        T1 = ?ELEMENT:pi1(Ty),
        T2 = ?ELEMENT:pi2(Ty),
        phi(ty_rec:diff(S1, T1), S2, N)
          andalso
          phi(S1, ty_rec:diff(S2, T2), N)
      end
  ).

normalize(Size, Ty, [], [], Fixed, M) ->
  dnf(Ty, {
    fun(Pos, Neg, T) ->
      case bdd_bool:empty() of
        T -> [[]];
        _ ->
          BigS = ?ELEMENT:big_intersect(Pos),
          phi_norm(Size, ?ELEMENT:pi1(BigS), ?ELEMENT:pi2(BigS), Neg, Fixed, M)
      end
    end,
    fun constraint_set:meet/2
  });
normalize(Size, DnfTy, PVar, NVar, Fixed, M) ->
  Ty = ty_rec:tuple(Size, dnf_var_ty_tuple:tuple(DnfTy)),
  % ntlv rule
  ty_variable:normalize(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:tuple(Size, dnf_var_ty_tuple:var(Var)) end, M).

phi_norm(_Size, S, T, [], Fixed, M) ->
  constraint_set:join(?F(ty_rec:normalize(S, Fixed, M)), ?F(ty_rec:normalize(T, Fixed, M)));
phi_norm(Size, S1, S2, [Ty | N], Fixed, M) ->
  T1 = ?F(ty_rec:normalize(S1, Fixed, M)),
  T2 = ?F(ty_rec:normalize(S2, Fixed, M)),

  T3 =
    ?F(begin
      TT1 = ty_tuple:pi1(Ty),
      TT2 = ty_tuple:pi2(Ty),
      X1 = ?F(phi_norm(Size, ty_rec:diff(S1, TT1), S2, N, Fixed, M)),
      X2 = ?F(phi_norm(Size, S1, ty_rec:diff(S2, TT2), N, Fixed, M)),
      constraint_set:meet(X1, X2)
    end),

  constraint_set:join(T1, ?F(constraint_set:join(T2, T3))).


apply_to_node(Node, Map, Memo) ->
  substitute(Node, Map, Memo, fun(N, S, M) -> ?ELEMENT:substitute(N, S, M) end).

