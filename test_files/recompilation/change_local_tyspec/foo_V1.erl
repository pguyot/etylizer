-module(foo).

-export([foo_fun/2]).

-spec helper(boolean()) -> boolean().
helper(X) -> true and X.

-spec foo_fun(boolean(), boolean()) -> boolean().
foo_fun(X, Y) -> bar:bar_fun(X) and helper(Y).

