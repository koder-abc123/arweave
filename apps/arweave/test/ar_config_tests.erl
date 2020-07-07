-module(ar_config_tests).
-include("src/ar_config.hrl").
-include_lib("eunit/include/eunit.hrl").

parse_test_() ->
	{timeout, 60, fun parse_config/0}.

parse_config() ->
	ExpectedMiningAddr = ar_util:decode(<<"LKC84RnISouGUw4uMQGCpPS9yDC-tIoqM2UVbUIt-Sw">>),
	{ok, ParsedConfig} = ar_config:parse(config_fixture()),
	?assertMatch(#config{
		benchmark = true,
		port = 1985,
		mine = true,
		peers = [
			{188,166,200,45,1984},
			{188,166,192,169,1984},
			{163,47,11,64,1984},
			{159,203,158,108,1984},
			{159,203,49,13,1984},
			{139,59,51,59,1984},
			{138,197,232,192,1984},
			{46,101,67,172,1984}
		],
		data_dir = "some_data_dir",
		metrics_dir = "metrics_dir",
		polling = true,
		auto_join = false,
		clean = true,
		diff = 42,
		mining_addr = ExpectedMiningAddr,
		max_miners = 43,
		new_key = true,
		load_key = "some_key_file",
		disk_space = 44*1024*1024*1024,
		used_space = _,
		start_from_block_index = true,
		internal_api_secret = <<"some_very_very_long_secret">>,
		enable = [feature_1, feature_2],
		disable = [feature_3, feature_4],
		content_policy_files = ["some_content_policy_1", "some_content_policy_2"],
		transaction_blacklist_files = ["some_blacklist_1", "some_blacklist_2"],
		gateway_domain = <<"gateway.localhost">>,
		gateway_custom_domains = [<<"domain1.example">>, <<"domain2.example">>],
		webhooks = [
			#config_webhook{
				events = [transaction, block],
				url = <<"https://example.com/hook">>,
				headers = [{<<"Authorization">>, <<"Bearer 123456">>}]
			}
		],
		max_connections = 512,
		max_gateway_connections = 64,
		disk_pool_data_root_expiration_time = 10000,
		max_disk_pool_buffer_mb = 100000,
		max_disk_pool_data_root_buffer_mb = 100000000
	}, ParsedConfig).

config_fixture() ->
	Dir = filename:dirname(?FILE),
	Path = filename:join(Dir, "ar_config_tests_config_fixture.json"),
	{ok, FileData} = file:read_file(Path),
	FileData.
