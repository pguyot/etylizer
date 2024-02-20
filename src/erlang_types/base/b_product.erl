-module(b_product).

-export([compare/2, equal/2, substitute/3, all_variables/1]).
-export([product/2, pi1/1, pi2/1, has_ref/2, transform/2, any/0, empty/0, big_intersect/1, is_empty/1]).

empty() -> {product, ty_rec:empty(), ty_rec:empty()}.
any() -> {product, ty_rec:any(), ty_rec:any()}.

compare(A, B) when A < B -> -1;
compare(A, B) when A > B -> 1;
compare(_, _) -> 0.

equal(P1, P2) -> compare(P1, P2) =:= 0.

product(A, B) -> {product, A, B}.

pi1({product, A, _}) -> A.
pi2({product, _, B}) -> B.

has_ref({product, A, B}, Ref) -> 
    ty_rec:has_ref(A, Ref) orelse ty_rec:has_ref(B, Ref).

is_empty({product, A, B}) ->
    ty_rec:is_empty(A) orelse ty_rec:is_empty(B).

transform({product, A, B}, #{to_tuple := ToTuple}) ->
    error(todo_transform),
    ToTuple([A,B]).

big_intersect([X]) -> X;
big_intersect([X | Y]) ->
    lists:foldl(fun({product, A, B}, {product, S, T}) ->
        {product, ty_rec:intersect(A, S), ty_rec:intersect(B, T)}
                end, X, Y).

substitute({product, A, B}, Map, Memo) ->
    {product, ty_rec:substitute(A, Map, Memo), ty_rec:substitute(B, Map, Memo)}.

all_variables({product, A, B}) ->
    ty_rec:all_variables(A) ++ ty_rec:all_variables(B).
