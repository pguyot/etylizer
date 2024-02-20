-module(ty_tuple).

%% n-tuple representation
-export([compare/2, equal/2, substitute/3, all_variables/1]).

-export([tuple/1, pi/2, has_ref/2, components/1, transform/3, transform/2, any/1, empty/1, big_intersect/1, is_empty/1]).

empty(Size) -> {ty_tuple, Size, [ty_rec:empty() || _ <- lists:seq(1, Size)]}.
any(Size) -> {ty_tuple, Size, [ty_rec:any() || _ <- lists:seq(1, Size)]}.

compare(A, B) when A < B -> -1;
compare(A, B) when A > B -> 1;
compare(_, _) -> 0.

equal(P1, P2) -> compare(P1, P2) =:= 0.

tuple(Refs) -> {ty_tuple, length(Refs), Refs}.

components({ty_tuple, _, Refs}) -> Refs.
pi(I, {ty_tuple, _, Refs}) -> lists:nth(I, Refs).
has_ref({ty_tuple, _, Refs}, Ref) -> length([X || X <- Refs, X == Ref]) > 0.

is_empty({ty_tuple, _, Refs}) ->
    lists:any(fun(T) -> ty_rec:is_empty(T) end, Refs).

transform({ty_tuple, _, Refs}, #{to_tuple := ToTuple}) ->
    ToTuple(Refs).

transform(4, {ty_tuple, _, [Left, Right]}, #{to_tuple := ToTuple}) ->
    {L1, L2} = is_only_two_tuple(Left),
    {R1, R2} = is_only_two_tuple(Right),
    ToTuple([L1, L2, R1, R2]);
transform(Length, T = {ty_tuple, _, Refs}, #{to_tuple := ToTuple}) ->
    error({todo_transform, Length, T}),
    ToTuple(Refs).


% HACK
-record(ty, {predef, atom, interval, list, tuple, function}).
is_only_two_tuple(TyRef) ->
    #ty{predef = A, atom = B, interval = I, list = L, tuple = {DT, MT}, function = {DF, MF}} = ty_ref:load(TyRef),
    true = dnf_var_predef:is_empty(A),
    true = dnf_var_ty_atom:is_empty(B),
    true = dnf_var_int:is_empty(I),
    true = dnf_var_ty_list:is_empty(L),
    true = dnf_var_ty_tuple:is_empty(DT),
    true = dnf_var_ty_function:is_empty(DF),
    [] = maps:keys(MF),
    [2] = maps:keys(MT),
    [] = dnf_var_ty_tuple:tlv(maps:get(2, MT)),
    % this is enforced
    {terminal, {node, {ty_tuple, 2, [LL, RR]}, {terminal, 1}, {terminal, 0}}} = maps:get(2, MT),
    {LL, RR}.

big_intersect([]) -> error(illegal_state);
big_intersect([X]) -> X;
big_intersect([X | Y]) ->
    lists:foldl(fun({ty_tuple, _, Refs}, {ty_tuple, Dim, Refs2}) ->
        true = length(Refs) == length(Refs2),
        {ty_tuple, Dim, [ty_rec:intersect(S, T) || {S, T} <- lists:zip(Refs, Refs2)]}
                end, X, Y).

substitute({ty_tuple, Dim, Refs}, Map, Memo) ->
    {ty_tuple, Dim, [ ty_rec:substitute(B, Map, Memo) || B <- Refs ] }.

all_variables({ty_tuple, _, Refs}) ->
    lists:flatten([ty_rec:all_variables(E) || E <- Refs]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

usage_test() ->
    % (int, int)
    TIa = ty_rec:interval(dnf_var_int:int(ty_interval:interval('*', '*'))),
    TIb = ty_rec:interval(dnf_var_int:int(ty_interval:interval('*', '*'))),

    _Ty_Tuple = ty_tuple:tuple([TIa, TIb]),

    ok.

-endif.
