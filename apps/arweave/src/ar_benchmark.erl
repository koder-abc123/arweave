-module(ar_benchmark).

-export([run/0]).

-include("src/ar.hrl").

%%% Runs a never ending mining performance benchmark.

%% @doc Execute the benchmark, printing the results to the terminal.
run() ->
	io:format(
		"~nRunning Arweave mining benchmark with ~B miner(s). "
		"Press Control+C twice to quit.~n~n",
		[ar_meta_db:get(max_miners)]
	),
	Key = crypto:strong_rand_bytes(32),
	ar_randomx_state:init(
		whereis(ar_randomx_state),
		ar_randomx_state:swap_height(ar_fork:height_2_0()),
		Key,
		erlang:system_info(schedulers_online)
	),
	loop({0, 0}, initial_diff()).

initial_diff() ->
	Diff = ar_retarget:switch_to_linear_diff(ar_meta_db:get(diff)),
	{_, TimeSpent} = mine(Diff, 10),
	%% The initial difficulty might be too easy
	%% for the machine so we mine 10 blocks and
	%% calibrate it before reporting the first result.
	switch_diff(Diff, TimeSpent).

loop({TotalHashesTried, TotalTimeSpent}, Difficulty) ->
	{HashesTried, TimeSpent} = mine(Difficulty, 10),
	NewDifficulty = switch_diff(Difficulty, TimeSpent),
	NewTotalHashesTried = TotalHashesTried + HashesTried,
	NewTotalTimeSpent = TotalTimeSpent + TimeSpent,
	io:format(
		"Current estimate: ~s. Since start: ~s~n",
		[
			format_hashes_per_second(HashesTried, TimeSpent),
			format_hashes_per_second(NewTotalHashesTried, NewTotalTimeSpent)
		]
	),
	loop({NewTotalHashesTried, NewTotalTimeSpent}, NewDifficulty).

mine(Diff, Rounds) ->
	{Time, HashesTried} = timer:tc(fun() ->
		Run = fun(_) -> mine(Diff) end,
		lists:sum(lists:map(Run, lists:seq(1, Rounds)))
	end),
	{HashesTried, Time}.

mine(Diff) ->
	B = #block{
		indep_hash = crypto:hash(sha384, crypto:strong_rand_bytes(40)),
		diff = Diff,
		hash = crypto:hash(sha384, crypto:strong_rand_bytes(40)),
		timestamp = os:system_time(seconds),
		last_retarget = os:system_time(seconds),
		hash_list = [],
		height = ar_fork:height_2_0()
	},
	ar_mine:start(B, #poa{}, [], unclaimed, [], self(), [], []),
	receive
		{work_complete, _, _, _, _, _, HashesTried} ->
			HashesTried
	end.

switch_diff(Diff, Time) ->
	MaxDiff = ar_mine:max_difficulty(),
	erlang:trunc(MaxDiff - (MaxDiff - Diff) * Time / 10000000).

format_hashes_per_second(Hashes, Time) ->
	TimeSec = Time / 1000000,
	HashesPerSec = Hashes / TimeSec,
	case HashesPerSec of
		N when N > 10000 ->
			MegaPerSec = HashesPerSec / 1000000,
			iolist_to_binary(io_lib:format("~.4f MH/s", [MegaPerSec]));
		_ ->
			iolist_to_binary(io_lib:format("~.4f H/s", [HashesPerSec]))
	end.
