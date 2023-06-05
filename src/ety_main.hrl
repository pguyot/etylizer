-record(opts, {log_level = default :: log:log_level() | default,
               help = false :: boolean(),
               dump_raw = false :: boolean(),
               dump = false :: boolean(),
               sanity = false :: boolean(),
               no_type_checking = false :: boolean(),
               only = [] :: [string()],
               ast_file = empty :: empty | string(),
               path = empty :: empty | string(),
               includes = [] :: [string()],
               defines = [] :: [{atom(), string()}],
               load_start = [] :: [string()],
               load_end = [] :: [string()],
               files = [] :: [string()]}).

-type cmd_opts() :: #opts{}.
