-module(constr_simp).

-include_lib("log.hrl").

-export([
    simp_constrs/2,
    new_ctx/4,
    sanity_check/2
]).

-export_type([
    unmatched_branch_mode/0,
    simp_constrs_result/0
]).

-record(ctx,
        { symtab :: symtab:t(),
          env :: constr:constr_poly_env(),
          tyvar_counter :: counters:counters_ref(),
          sanity :: t:opt(ast_check:ty_map()),
          unmatched_branch :: unmatched_branch_mode()
        }).
-type ctx() :: #ctx{}.

% Mode ignore_branch specifies that branches of a case that cannot be matched
% are excluded while type-checking.

% Mode report should report an error in case a branch cannot be match.
%
% When type-checking a function against an intersection type, we use mode
% ignore_branch. Otherwise, we use report.
%
% Currently, it is not possible to check for unmatched branches when type-checking
% against an intersection type. Here, we could report an error if the same branch
% is excluded for every element of the intersection. But this is not implemented.
-type unmatched_branch_mode() :: ignore_branch | report.

-spec new_ctx(symtab:t(), constr:constr_poly_env(),
              t:opt(ast_check:ty_map()), unmatched_branch_mode()) -> ctx().
new_ctx(Tab, Env, Sanity, BranchMode) ->
    Counter = counters:new(1, []),
    Ctx = #ctx{ tyvar_counter = Counter, env = Env, symtab = Tab, sanity = Sanity,
                unmatched_branch = BranchMode },
    Ctx.

% The result of constraint simplication is either a single error or potentially several sets
% of subtyping constraints (there is at least one such set). A solution to any of these sets
% is a solution to the original constraint problem.
-type simp_constrs_result() ::
    {simp_constrs_ok, nonempty_list(constr:simp_constrs())} |
    {simp_constrs_error, {simp_constrs_error_kind(), ast:loc()}}.

-spec zero_simp_constrs_result() -> simp_constrs_result().
zero_simp_constrs_result() -> {simp_constrs_ok, [sets:new()]}.

-type simp_constrs_error_kind() :: tyerror | redundant_branch | non_exhaustive_case.

-spec is_simp_constrs_error(simp_constrs_result()) -> boolean().
is_simp_constrs_error({simp_constrs_error, _}) -> true;
is_simp_constrs_error(_) -> false.

-type simp_constrs_cont() :: fun((simp_constrs_result(), nonempty_list(constr:simp_constrs())) -> simp_constrs_result()).

-spec simp_constrs_if_ok(simp_constrs_result(), simp_constrs_cont()) -> simp_constrs_result().
simp_constrs_if_ok({simp_constrs_ok, L} = C, F) -> F(C, L);
simp_constrs_if_ok(X, _) -> X.

simp_constrs_if_ok2({simp_constrs_ok, []}, F) -> error(todo_empty);
simp_constrs_if_ok2({simp_constrs_ok, [Ds]}, F) -> 
    io:format(user,"Single solution...~n", []),
    F(Ds);
simp_constrs_if_ok2({simp_constrs_ok, [Ds, Ds2 | Dss]}, F) -> 
    io:format(user,"Multi cont...~n", []),
    SingleResults = F(Ds),
    case SingleResults of
        {simp_constrs_error, _} -> 
            simp_constrs_if_ok2([Ds2 | Dss], F);
        _ -> 
            Other = simp_constrs_if_ok2([Ds2 | Dss], F),
            ?LOG_INFO("~p", [Other]),
            cross_union(SingleResults, Other)
    end;
simp_constrs_if_ok2(X, _) -> 
    io:format(user,"ERROR...~n", []),
    X.

simp_tally_if_ok({error, _}, Locs, Cont) -> Cont(no_solution);
simp_tally_if_ok([], Locs, Cont) -> Cont(no_solution);
simp_tally_if_ok([Sol | Sols], Locs, Cont) -> 
    Solx = get_subst(Sol, Locs),
    Res = Cont(Solx),
    case Res of
        {simp_constrs_error, _} -> simp_tally_if_ok(Sols, Locs, Cont);
        _ -> Res % return solution
    end.

-spec cross_union(simp_constrs_result(), simp_constrs_result()) -> simp_constrs_result().
cross_union({simp_constrs_error, _} = Err, _) -> Err;
cross_union(_, {simp_constrs_error, _} = Err) -> Err;
cross_union({simp_constrs_ok, L1}, {simp_constrs_ok, L2}) ->
    ResultList = lists:flatmap(
      fun(S1) ->
              lists:map(fun(S2) -> sets:union(S1, S2) end, L2)
      end,
      L1),
    {simp_constrs_ok, ResultList}.

-spec simp_constrs(ctx(), constr:constrs()) -> simp_constrs_result().
simp_constrs(Ctx, Cs) ->
    ?LOG_TRACE("simp_constrs, Cs=~w", Cs),
    sets:fold(
      fun(C, Dss2) ->
        simp_constrs_if_ok(Dss2,
            fun(_, _) ->
                Dss1 = simp_constr(Ctx, C),
                case Ctx#ctx.sanity of
                    {ok, TyMap} -> sanity_check(Dss1, TyMap);
                    error -> ok
                end,
                cross_union(Dss1, Dss2)
            end)
      end,
      zero_simp_constrs_result(), Cs).


list_ds([], Ctx, All, Cont) -> Cont(All);
list_ds([{BodyLocs, {GuardsGammaI, GuardCsI}, {BodyGammaI, BodyCsI}, CIwhen}], Ctx, All, Cont) -> 
    simp_constrs_if_ok2(simp_constrs(Ctx, CIwhen), fun(D) -> list_ds([], Ctx, [{BodyLocs, {GuardsGammaI, GuardCsI}, {BodyGammaI, BodyCsI}, D} | All], Cont) end);
list_ds([{BodyLocs, {GuardsGammaI, GuardCsI}, {BodyGammaI, BodyCsI}, CIwhen} | Cs], Ctx, All, Cont) ->
    simp_constrs_if_ok2(simp_constrs(Ctx, CIwhen), fun(D) -> 
        list_ds(Cs, Ctx, [{BodyLocs, {GuardsGammaI, GuardCsI}, {BodyGammaI, BodyCsI}, D} |All], Cont) 
    end).

list_tally([], Locs, DsScrut, Ctx, All, Cont) -> Cont(All);
list_tally([{BodyLocs, {GuardsGammaI, GuardCsI}, {BodyGammaI, BodyCsI}, DIwhen} | Next], Locs, DsScrut, Ctx, All, Cont) ->
    ?LOG_INFO("Checking branch solutions for:~n~s", pretty:render_constr(sets:union(DIwhen, DsScrut))),
    % returns a single thehta_j (backtracks) or none
    simp_tally_if_ok(tally:tally(Ctx#ctx.symtab, sets:union(DsScrut, DIwhen)), Locs, 
    fun
        ({Subst, EquivDs}) -> 
            % found solution, generate Ci -> Di with new context
            NewGuardsCtx = inter_env(Ctx, apply_subst_to_env(Subst, GuardsGammaI)),
            simp_constrs_if_ok2(simp_constrs(NewGuardsCtx, GuardCsI), fun(GuardDi) -> 
                ?LOG_INFO("Not ignoring branch at ~s", ast:format_loc(loc(BodyLocs))),
                % here we have a valid Di
                % descend into the body
                NewBodyCtx = inter_env(Ctx, apply_subst_to_env(Subst, BodyGammaI)),
                simp_constrs_if_ok2(simp_constrs(NewBodyCtx, BodyCsI), fun(BodyDsI) -> 
                    list_tally(Next, Locs, DsScrut, Ctx, All ++ [{EquivDs, GuardDi, BodyDsI}], Cont)
                end)
            end);
        (no_solution) -> 
            % here we skip the branch at Di = 0
            % TODO print constrs
            ?LOG_INFO("Ignoring branch at ~s, D U D_i equivalent to none()", ast:format_loc(loc(BodyLocs))),
            % guard di is then empty
            list_tally(Next, Locs, DsScrut, Ctx, All ++ [{empty}], Cont)
    end).

-spec simp_constr(ctx(), constr:constr()) -> simp_constrs_result().
simp_constr(Ctx, C) ->
    ?LOG_TRACE("simp_constr, C=~w", C),
    case C of
        {csubty, _, _, _} -> {simp_constrs_ok, [single(C)]};
        {cvar, Locs, X, T} ->
            PolyTy =
                case maps:find(X, Ctx#ctx.env) of
                    {ok, U} -> U;
                    error ->
                        case X of
                            {local_ref, Y} ->
                                errors:bug("Unbound variable in constraint simplification ~w", Y);
                            GlobalX ->
                                symtab:lookup_fun(GlobalX, loc(Locs), Ctx#ctx.symtab)
                        end
                end,
            {simp_constrs_ok, [single({csubty, Locs, fresh_ty_scheme(Ctx, PolyTy), T})]};
        {cop, Locs, OpName, OpArity, T} ->
            PolyTy = symtab:lookup_op(OpName, OpArity, loc(Locs), Ctx#ctx.symtab),
            {simp_constrs_ok, [single({csubty, Locs, fresh_ty_scheme(Ctx, PolyTy), T})]};
        {cdef, _Locs, Env, Cs} ->
            NewCtx = extend_env(Ctx, Env),
            simp_constrs(NewCtx, Cs);
        {ccase, Locs, CsScrut, {ExhauLeft, ExhauRight}, Bodies} ->
            case Ctx#ctx.sanity of
                {ok, TyMap0} ->
                    constr_gen:sanity_check(CsScrut, TyMap0);
                error -> ok
            end,
            ?LOG_INFO("Solving constraints for scrutiny of case at ~s in order to check " ++
                        "which branches should be ignored.~n" ++
                        "Env: ~s~nConstraints for scrutiny:~n~s~n" ++
                        "exhaustivness check: ~s <= ~s",
                        ast:format_loc(loc(Locs)),
                        pretty:render_poly_env(Ctx#ctx.env),
                        pretty:render_constr(CsScrut),
                        pretty:render_ty(ExhauLeft),
                        pretty:render_ty(ExhauRight)),

            simp_constrs_if_ok2(simp_constrs(Ctx, CsScrut), fun(DsScrutWEx) -> 
                ?LOG_INFO("Checking solution for scrutiny of case at ~s in order to check " ++
                        "which branches should be ignored.~n" ++
                        "Env: ~s~nConstraints for scrutiny:~n~s~n" ++
                        "exhaustivness check: ~s <= ~s",
                        ast:format_loc(loc(Locs)),
                        pretty:render_poly_env(Ctx#ctx.env),
                        pretty:render_constr(DsScrutWEx),
                        pretty:render_ty(ExhauLeft),
                        pretty:render_ty(ExhauRight)),

                % TODO does backtracking and multiple solutions work?
                % TODO Exhau missing from rule?
                Exhau = sets:from_list([{csubty, Locs, ExhauLeft, ExhauRight}]),
                DsScrut = sets:union([DsScrutWEx]),

                ?LOG_INFO("Checking all branches with tally"),
                list_ds(Bodies, Ctx, [], 
                    fun(AllBodiesWithDis) ->
                        % now we have all D_i
                        % get all tally theta_j (with equiv sets)
                        list_tally(lists:reverse(AllBodiesWithDis), Locs, DsScrut, Ctx, [], 
                        fun(EquivDiDiList) -> 
                            % now we have all theta_j and equiv(theta_j)
                            lists:foldl( fun
                                ({empty}, AccDs) -> 
                                    % skip this branch
                                    AccDs; 
                                ({EquivDsi, GuardDsi, BodyDsi}, AccDs) -> 
                                    % use this branch
                                    % TODO BodyDsi not in rule?
                                    cross_union(singleds(sets:union(EquivDsi, sets:union(GuardDsi, BodyDsi))), AccDs)
                            end, zero_simp_constrs_result(), EquivDiDiList)
                        end)
                    end
                )
            end);
        {cunsatisfiable, Locs, Msg} -> [single({cunsatisfiable, Locs, Msg})];
        X -> errors:uncovered_case(?FILE, ?LINE, X)
    end.

-spec fresh_tyvar(ctx(), ast:ty_varname()) -> ast:ty_varname().
fresh_tyvar(Ctx, Base) ->
    I = counters:get(Ctx#ctx.tyvar_counter, 1),
    counters:add(Ctx#ctx.tyvar_counter, 1, 1),
    S = utils:sformat("~w@~w", Base, I),
    list_to_atom(S).

-spec fresh_ty_scheme(ctx(), ast:ty_scheme()) -> ast:ty().
fresh_ty_scheme(_Ctx, {ty_scheme, [], T}) -> T;
fresh_ty_scheme(Ctx, {ty_scheme, Tyvars, T}) ->
    L =
        lists:map(
          fun({Alpha, Bound}) ->
                  Fresh = fresh_tyvar(Ctx, Alpha),
                  {Alpha, {intersection, [{var, Fresh}, Bound]}}
          end,
          Tyvars
         ),
    Subst = subst:from_list(L),
    subst:apply(Subst, T).

-spec single(T) -> sets:set(T).
single(X) -> sets:from_list([X]).

singleds(X) ->
    {simp_constrs_ok, [X]}.

-spec loc(constr:locs()) -> ast:loc().
loc(Locs) ->
    case loc(Locs, error) of
        error -> errors:bug("empty set of locations");
        X -> X
    end.

-spec loc(constr:locs() | sets:set(ast:loc()), T) -> T | ast:loc().
loc({_, Locs}, Def) -> loc(Locs, Def);
loc(Locs, Def) ->
    case sets:to_list(Locs) of
        [First | Rest] ->
            lists:foldl(fun ast:min_loc/2, First, Rest);
        [] -> Def
    end.

-spec locs_from_constrs(constr:constrs()) -> sets:set(ast:loc()).
locs_from_constrs(Cs) ->
    sets:union(
        lists:map(
            fun (C) ->
                case C of
                    {csubty, {_, Locs}, _, _} -> Locs;
                    {cvar, {_, Locs}, _, _} -> Locs;
                    {cop, {_, Locs}, _, _, _} -> Locs;
                    {cdef, {_, Locs}, _, _} -> Locs;
                    {ccase, {_, Locs}, _, _, _} -> Locs;
                    {cunsatisfiable, L, _} -> sets:from_list([L])
                end
            end, sets:to_list(Cs))
    ).

-spec get_substs([subst:t()], constr:locs()) -> [{subst:t(), constr:simp_constrs()}].
get_substs(Substs, Locs) ->
    case Substs of
        {error, _} ->
            % We cannot throw an error here because other branches might return a solvable constraint
            % set.
            [];
        L ->
            lists:map(
              fun(Subst) ->
                      Alphas = subst:domain(Subst),
                      EquivCs =
                          lists:foldl(
                            fun(Alpha, Acc) ->
                                    T = subst:apply(Subst, {var, Alpha}),
                                    sets:add_element(
                                      {csubty, Locs, T, {var, Alpha}},
                                      sets:add_element({csubty, Locs, {var, Alpha}, T}, Acc))
                            end,
                            sets:new(),
                            Alphas),
                        io:format(user, "~p~n~p~n", [Subst, EquivCs]),
                      {Subst, EquivCs}
              end,
              L
             )
    end.

get_subst(Subst, Locs) ->
    case Subst of
        {error, _} ->
            % We cannot throw an error here because other branches might return a solvable constraint
            % set.
            [];
        _L ->
            Alphas = subst:domain(Subst),
            EquivCs =
                lists:foldl(
                fun(Alpha, Acc) ->
                        T = subst:apply(Subst, {var, Alpha}),
                        sets:add_element(
                            {csubty, Locs, T, {var, Alpha}},
                            sets:add_element({csubty, Locs, {var, Alpha}, T}, Acc))
                end,
                sets:new(),
                Alphas),
            {Subst, EquivCs}
    end.

-spec extend_env(ctx(), constr:constr_env()) -> ctx().
extend_env(Ctx, Env) ->
    PolyEnv =
        maps:map(fun(_Key, T) -> {ty_scheme, [], T} end, Env),
    NewEnv = maps:merge(Ctx#ctx.env, PolyEnv), % values from the second parameter have precedence
    ?LOG_TRACE("extend_env(~s, ~s) = ~s",
        pretty:render_poly_env(Ctx#ctx.env),
        pretty:render_mono_env(Env),
        pretty:render_poly_env(NewEnv)),
    Ctx#ctx { env = NewEnv }.

-spec inter_env(ctx(), constr:constr_env()) -> ctx().
inter_env(Ctx, Env) ->
    PolyEnv =
        maps:map(fun(_Key, T) -> {ty_scheme, [], T} end, Env),
    Combiner =
        fun (_Key, {ty_scheme, [], OldTy}, {ty_scheme, [], NewTy}) ->
            {ty_scheme, [], stdtypes:tinter(OldTy, NewTy)};
            (_Key, OldTy, NewTy) ->
                ?ABORT("BUG: inter_env, cannot combine polymorphic types ~s and ~s",
                    pretty:render_tyscheme(OldTy), pretty:render_tyscheme(NewTy))
        end,
    NewEnv = maps:merge_with(Combiner, Ctx#ctx.env, PolyEnv), % values from the second parameter have precedence
    ?LOG_TRACE("inter_env(~s, ~s) = ~s",
        pretty:render_poly_env(Ctx#ctx.env),
        pretty:render_mono_env(Env),
        pretty:render_poly_env(NewEnv)),
    Ctx#ctx { env = NewEnv }.

-spec apply_subst_to_env(subst:t(), constr:constr_env()) -> constr:constr_env().
apply_subst_to_env(Subst, Env) ->
    maps:map(fun(_Key, T) -> subst:apply(Subst, T) end, Env).

-spec sanity_check(any(), ast_check:ty_map()) -> ok.
sanity_check({simp_constrs_ok, Dss}, Spec) ->
    if
        not is_list(Dss) -> ?ABORT("List of constraint sets is not a list: ~w", Dss);
        true ->
            lists:foreach(
              fun(Ds) ->
                    case sets:is_set(Ds) of
                        false ->
                            ?ABORT("Expected set of simple constraints, got ~w", Ds);
                        true ->
                            lists:foreach(
                            fun(D) ->
                                    case ast_check:check_against_type(Spec, constr, simp_constr, D) of
                                        true ->
                                            ok;
                                        false ->
                                            ?ABORT("Invalid simple constraint generated: ~w", D)
                                    end
                            end,
                            sets:to_list(Ds))
                    end
              end,
              Dss)
    end;
sanity_check(_, _) -> ok.
