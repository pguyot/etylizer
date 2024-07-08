% A generic DNF representation using lines parameterized over 'terminal elements: Line<Terminal>
%
% A line represents a intersection of 'terminal types.
% Multiple lines represent a union of lines.
% 
% Each line tracks positive and negative variables, and consists of a positive and negative literals.
% A 'Any' line is represented as [[]]
% A 'Empty' line is represented as []

-export([has_ref/2, get_dnf/1, any/0, empty/0, equal/2, node/1, terminal/1, compare/2, union/2, intersect/2, negate/1, negate/2, diff/2]).

% these are defined here so the IDE does not complain
-ifndef(TERMINAL).
-define(TERMINAL, bdd_bool).
-endif.

any() -> [[]].
empty() -> [].

equal(L1, L2) -> L1 =:= L2.

pos(Atom) -> [{[], [], [Atom], []}].
neg(Atom) -> [{[], [], [], [Atom]}].
pos_var(Var) -> [{[Var], [], [], []}].
neg_var(Var) -> [{[], [Var], [], []}].

union(A, B) -> lists:uniq(A ++ B). 

intersect(A, B) -> 
  [{
    lists:uniq(PV1 ++ PV2), 
    lists:uniq(NV1 ++ NV2), 
    lists:uniq(P1 ++ P2), 
    lists:uniq(N1 ++ N2)
  } || {PV1, NV1, P1, N1} <- A, {PV2, NV2, P2, N2} <- B].

% TODO cont HERE
-spec negate_flag_dnf(dnf(flag()), memo()) -> dnf(flag()).
negate_flag_dnf(Dnf, _Memo) -> % memo not needed as signs are flipped
  % for each line (Pos, Neg), we flip the atom signs
  % for two flipped lines, we intersect them
  dnf(Dnf, {
    fun(Pv, Nv, P, N) -> 
      [X | Xs] = [negated_flag() || true <- P] ++ [flag() || true <- N],
      lists:foldl(fun(E, Acc) -> union(E, Acc) end, X, Xs)
    end, 
    fun(Line1, Line2) -> intersect(Line1, Line2) end
  }).

-spec negate_product_dnf(dnf(product()), memo()) -> dnf(product()).
negate_product_dnf(Dnf, _Memo) -> % memo not needed as signs are flipped
dnf(Dnf, {fun(P, N) -> 
    [X | Xs] = [negated_product(T) || T <- P] ++ [product(T) || T <- N],
    lists:foldl(fun(E, Acc) -> union_dnf(E, Acc) end, X, Xs)
  end, fun(Dnf1, Dnf2) -> intersect_dnf(Dnf1, Dnf2) end}).


diff(A, B) -> intersect(A, negate(B)).

s_is_any({terminal, Ty}) -> ?TERMINAL:equal(Ty, ?TERMINAL:any());
s_is_any(_) -> false.

s_is_empty({terminal, Ty}) -> ?TERMINAL:equal(Ty, ?TERMINAL:empty());
s_is_empty(_) -> false.

is_empty_union(F1, F2) ->
  F1() andalso F2().

get_dnf(Bdd) ->
  lists:filter(
    fun({_,_,[]}) -> false; ({_, _, T}) ->
      case ?TERMINAL:empty() of
        T -> false;
        _ ->  true
      end
    end,
    dnf(Bdd, {fun(P, N, T) -> [{P, N, T}] end, fun(C1, C2) -> C1() ++ C2() end})
  ).


dnf(Bdd, {ProcessCoclause, CombineResults}) ->
  do_dnf(Bdd, {ProcessCoclause, CombineResults}, _Pos = [], _Neg = []).

do_dnf({node, Element, Left, Right}, F = {_Process, Combine}, Pos, Neg) ->
  % heuristic: if Left is positive & 1, skip adding the negated Element to the right path
  % TODO can use the see simplifications done in ty_rec:transform to simplify DNF before processing?
  case {terminal, ?TERMINAL:any()} of
    Left ->
      F1 = fun() -> do_dnf(Left, F, [Element | Pos], Neg) end,
      F2 = fun() -> do_dnf(Right, F, Pos, Neg) end,
      Combine(F1, F2);
    _ ->
      F1 = fun() -> do_dnf(Left, F, [Element | Pos], Neg) end,
      F2 = fun() -> do_dnf(Right, F, Pos, [Element | Neg]) end,
      Combine(F1, F2)
  end;
do_dnf({terminal, Terminal}, {Proc, _Comb}, Pos, Neg) ->
  Proc(Pos, Neg, Terminal).


has_ref(Ty, Ref) ->
  dnf(Ty, {
    fun
      (P,N,T) ->
        Fun = fun(F) -> ?ELEMENT:has_ref(F, Ref) end,
        ?TERMINAL:has_ref(T, Ref) orelse
          lists:any(Fun, P) orelse
          lists:any(Fun, N)
    end,
    fun(F1, F2) -> F1() orelse F2() end
  }).

all_variables(Ty, M) ->
  dnf(Ty, {
    fun
      (P,N,T) ->
        ?TERMINAL:all_variables(T, M) ++
          lists:foldl(fun(L, Acc) -> Acc ++ ?ELEMENT:all_variables(L, M) end, [], P) ++
          lists:foldl(fun(L, Acc) -> Acc ++ ?ELEMENT:all_variables(L, M) end, [], N)
    end,
    fun(F1, F2) -> lists:usort(F1() ++ F2()) end
  }).


transform(Ty, Ops = #{negate := Negate, intersect := Intersect, union := Union}) ->
  dnf(Ty, {
    fun
      (P,N,T) ->
        P1 = ?TERMINAL:transform(T, Ops),
        P2 = [?ELEMENT:transform(V, Ops) || V <- P],
        P3 = [Negate(?ELEMENT:transform(V, Ops)) || V <- N],
        Intersect([P1] ++ P2 ++ P3)
    end,
    fun(F1, F2) -> Union([F1(), F2()]) end
  }).
