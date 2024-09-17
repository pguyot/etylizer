-module(dnf_var_predef).

-define(ELEMENT, ty_variable).
-define(TERMINAL, ty_predef).

-export([to_line/1, apply_to_node/3]).
-export([is_empty/1, normalize/3, substitute/4]).
-export([var/1, predef/1,  all_variables/2, transform/2]).

-export_type([type/0]).
-type type() :: term(). %TODO

-include("bdd_var.hrl").

to_line(Predef) ->
  dnf(Predef, {
    fun
      (P,N,T) ->
        P1 = ?TERMINAL:to_line(T),
        P2 = [?ELEMENT:to_line(V) || V <- P],
        P3 = [?ELEMENT:to_line(V) || V <- N],
        [{P2, P3, P1, []}]
    end,
    fun(F1, F2) -> F1 ++ F2 end
  }).

print_ty(PredefVarDnf) ->
  dnf(PredefVarDnf, {
    fun
      (PVars,NVars,T) ->
        TerminalDoc = ?TERMINAL:print_ty(T),
        P2 = [?ELEMENT:print_ty(V) || V <- PVars],
        P3 = [?ELEMENT:print_ty(V) || V <- NVars],
        % [{P2, P3, P1, []}]
        TerminalDoc
    end,
    fun(Doc1, Doc2) -> epretty:beside(Doc1, Doc2) end
  }).

% generic
predef(Predef) -> terminal(Predef).
var(Var) -> node(Var).

% partially generic
is_empty(TyBDD) -> dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).
is_empty_coclause(_Pos, _Neg, T) -> ty_predef:is_empty(T).

normalize(Ty, Fixed, M) -> dnf(Ty, {
  fun(Pos, Neg, Atom) -> ty_predef:normalize(Atom, Pos, Neg, Fixed, M) end,
  fun constraint_set:meet/2
}).

% not recursive, no op substitution
apply_to_node(Node, _StdMap, _Memo) ->
  Node.
