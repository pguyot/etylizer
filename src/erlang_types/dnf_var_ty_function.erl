-module(dnf_var_ty_function).

-define(ELEMENT, ty_variable).
-define(TERMINAL, dnf_ty_function).
-define(F(Z), fun() -> Z end).


-export([is_empty/1]).
-export([normalize/4, substitute/4]).
-export([var/1, function/1, all_variables/2, mall_variables/2, transform/2]).

-include("bdd_var.hrl").

function(Tuple) -> terminal(Tuple).
var(Var) -> node(Var).

mall_variables({Default, Others}, M) when is_map(Others) ->
  lists:usort(lists:flatten(
    all_variables(Default, M) ++
    lists:map(fun({_K,V}) -> all_variables(V, M) end, maps:to_list(Others))
  ));
mall_variables(Ty, M) -> all_variables(Ty, M).

is_empty(TyBDD) -> dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).
is_empty_coclause(_Pos, _Neg, T) -> dnf_ty_function:is_empty(T).

normalize(Size, Ty, Fixed, M) -> 
  {Time2, Sol2} = timer:tc(fun() -> 
    dnf(Ty, {
      fun(Pos, Neg, DnfTy) -> normalize_coclause(Size, Pos, Neg, DnfTy, Fixed, M) end,
      fun constraint_set:meet/2
    })
  end),
  {Time, Sol} = timer:tc(fun() -> 
    Dnf = simplify(get_full_dnf(Ty)),
    lists:foldl(fun({Pos, Neg, DnfTy}, Acc) -> 
      OtherLazy = fun() -> normalize_coclause(Size, Pos, Neg, DnfTy, Fixed, M) end,
      constraint_set:meet(Acc, OtherLazy)
    end, [[]], Dnf)
  end),
  case Time > 1000 orelse Time2 > 1000 of
    true -> io:format(user,"~p vs ~p (~p)~n",[Time, Time2, Time/Time2]);
    _ -> ok
  end,
  Sol.
  

normalize_coclause(Size, PVar, NVar, Function, Fixed, M) ->
  case dnf_ty_function:empty() of
    Function -> [[]];
    _ ->
      case ty_ref:is_normalized_memoized({PVar, NVar, Function}, Fixed, M) of
        true ->
          [[]];
        miss ->
          dnf_ty_function:normalize(Size, Function, PVar, NVar, Fixed, sets:union(M, sets:from_list([{PVar, NVar, Function}])))
      end
  end.


% substitution delegates to dnf_ty_tuple substitution
apply_to_node(Node, Map, Memo) ->
  dnf_ty_function:substitute(Node, Map, Memo, fun(N, Subst, M) -> ty_function:substitute(N, Subst, M) end).


simplify([]) -> [];
simplify(DnfFun) ->
  NonVars = lists:flatten([P ++ N || {_, _, P, N} <- DnfFun, length(P ++ N) > 0]),
  % function constructor needs arity, and arity is implicit in the function BDD
  % for BDDs with only variables and no function part, we skip the simplification step
  case NonVars of
    [] -> back_to_bdd(DnfFun); % only contains variable parts
    [F | _] ->

  % otherwise, we can extract the arity from any clause
  Arity = length(ty_function:domains(F)),

  % Check if any summand is 0
  begin
    lists:foreach(fun
      ({Pvar, Nvar, Pos, Neg}) -> 
        Ty = ty_rec:of_function_dnf(Arity, Pvar, Nvar, Pos, Neg),
        case ty_rec:is_empty(Ty) of true -> error(todo); _ -> ok end,
        ok
    end, DnfFun)
  end,

  % check useless summands
  begin
    lists:foreach(fun
      ({Pvar, Nvar, Pos, Neg}) -> 
        % Dnf without
        D1 = DnfFun -- [{Pvar, Nvar, Pos, Neg}],

        TyWithout = ty_rec:of_function_dnfs(Arity, D1),
        TyWith = ty_rec:of_function_dnfs(Arity, DnfFun),

        case ty_rec:is_subtype(TyWith, TyWithout) of true -> 
          io:format(user, "Summand is useless!~n~s~nis contained in bigger type~n~s~n", [ty_rec:print(TyWith), ty_rec:print(TyWithout)]),
          error(todo); 
          _ -> ok 
        end,
        ok
    end, DnfFun)
  end,

  % TODO check useless literals
  
  % TODO merge comain, codomain
  
  % TODO apply recursively? (not needed for now)


  back_to_bdd(DnfFun)
  end.


% TODO can be polymorphic, put into bdd_var.hrl
-spec back_to_bdd([
  {[PosVars :: term()], [NegVars :: term()], [Pos :: term()], [Neg :: term()]}
]) -> [{PosVars :: term(), NegVars :: term(), InnerBdd :: term()}].
back_to_bdd([]) -> error(no);
back_to_bdd([{Pv, Nv, P, N}]) -> 
  L3 = [?TERMINAL:node(T) || T <- P],
  L4 = [?TERMINAL:negate(?TERMINAL:node(T)) || T <- N],
  [{Pv, Nv, lists:foldl(fun(E, Acc) -> ?TERMINAL:intersect(E, Acc) end, ?TERMINAL:any(), L3 ++ L4)}];
back_to_bdd([{Pv, Nv, P, N} | Rest]) -> 
  Clause = back_to_bdd([{Pv, Nv, P, N}]),
  Other = back_to_bdd(Rest),
  Clause ++ Other.