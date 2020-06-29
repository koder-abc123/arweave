-module(ar_patricia_tree).

-export([
	new/0,
	insert/3,
	get/2,
	compute_hash/2,
	foldr/3,
	is_empty/1,
	from_proplist/1
]).

-include_lib("eunit/include/eunit.hrl").

%%%===================================================================
%%% Public interface.
%%%===================================================================

new() ->
	#{ root => {no_parent, no_children, no_hash, no_prefix, no_value} }.

insert(Key, Value, Tree) ->
	{no_parent, Children, _Hash, no_prefix, no_value} = maps:get(root, Tree),
	InvalidatedHashRoot = {no_parent, Children, no_hash, no_prefix, no_value},
	insert(Key, Value, Tree#{ root => InvalidatedHashRoot }, 1, root).

get(Key, Tree) when is_binary(Key) ->
	get(Key, Tree, 1);
get(_, _) ->
	not_found.

compute_hash(Tree, HashFun) ->
	compute_hash(Tree, HashFun, root).

foldr(Fun, Acc, Tree) ->
	case is_empty(Tree) of
		true ->
			[];
		false ->
			foldr(Fun, Acc, Tree, root)
	end.

is_empty(Tree) ->
	maps:size(Tree) == 1.

from_proplist(Proplist) ->
	lists:foldl(
		fun({Key, Value}, Acc) -> ar_patricia_tree:insert(Key, Value, Acc) end,
		new(),
		Proplist
	).

%%%===================================================================
%%% Private functions.
%%%===================================================================

insert(Key, Value, Tree, Level, Parent) ->
	KeySize = byte_size(Key),
	KeyPrefix = case Key of <<>> -> <<>>; _ -> binary:part(Key, {0, Level}) end,
	KeySuffix = case Key of <<>> -> <<>>; _ -> binary:part(Key, {Level, KeySize - Level}) end,
	case maps:get(KeyPrefix, Tree, not_found) of
		{NodeParent, NodeChildren, NodeHash, NodeSuffix, NodeValue} ->
			Len = binary:longest_common_prefix([KeySuffix, NodeSuffix]),
			NodeSuffixSize = byte_size(NodeSuffix),
			KeySuffixSize = byte_size(KeySuffix),
			FullSuffixMatch = KeySuffix == NodeSuffix,
			Recurse = KeySuffixSize > NodeSuffixSize andalso NodeSuffixSize == Len,
			case {FullSuffixMatch, Recurse} of
				{true, false} ->
					UpdatedNode = {Parent, no_children, no_hash, KeySuffix, {v, Value}},
					Tree#{
						KeyPrefix => UpdatedNode
					};
				{false, true} ->
					InvalidatedHashNode =
						{NodeParent, NodeChildren, no_hash, NodeSuffix, NodeValue},
					insert(
						Key,
						Value,
						Tree#{
							KeyPrefix => InvalidatedHashNode
						},
						Level + NodeSuffixSize + 1,
						KeyPrefix
					);
				{false, false} ->
					PivotSuffix = binary:part(NodeSuffix, {0, Len}),
					{UpdatedNodePrefix, UpdatedNodeSuffix} =
						update_prefix(NodeSuffix, NodeSuffixSize, Len, KeyPrefix, PivotSuffix),
					UpdatedNode =
						{KeyPrefix, NodeChildren, NodeHash, UpdatedNodeSuffix, NodeValue},
					{NewNodePrefix, NewNodeSuffix} =
						update_prefix(KeySuffix, KeySuffixSize, Len, KeyPrefix, PivotSuffix),
					NewNode = {KeyPrefix, no_children, no_hash, NewNodeSuffix, {v, Value}},
					PivotChildren = gb_sets:from_list([UpdatedNodePrefix, NewNodePrefix]),
					PivotValue =
						case Len == NodeSuffixSize of
							true ->
								NodeValue;
							false ->
								no_value
						end,
					PivotNode = {NodeParent, PivotChildren, no_hash, PivotSuffix, PivotValue},
					Tree#{
						NewNodePrefix => NewNode,
						UpdatedNodePrefix => UpdatedNode,
						KeyPrefix => PivotNode
					}
			end;
		not_found ->
			NewNode = {Parent, no_children, no_hash, KeySuffix, {v, Value}},
			{NextParent, Children, _Hash, NextSuffix, ParentValue} = maps:get(Parent, Tree),
			UpdatedChildren =
				case Children of
					no_children ->
						gb_sets:from_list([KeyPrefix]);
					_ ->
						gb_sets:insert(KeyPrefix, Children)
				end,
			Tree#{
				KeyPrefix => NewNode,
				Parent => {NextParent, UpdatedChildren, no_hash, NextSuffix, ParentValue}
			}
	end.

update_prefix(Suffix, SuffixSize, CommonPrefixLen, Prefix, PivotSuffix) ->
	case binary:part(Suffix, {CommonPrefixLen, SuffixSize - CommonPrefixLen}) of
		<<>> ->
			{<< Prefix/binary, PivotSuffix/binary >>, <<>>};
		S ->
			FirstByte = binary:part(S, {0, 1}),
			NewPrefix = << Prefix/binary, PivotSuffix/binary, FirstByte/binary >>,
			{NewPrefix, binary:part(S, {1, SuffixSize - CommonPrefixLen - 1})}
	end.

get(Key, Tree, Level) ->
	KeyPrefix = case Key of <<>> -> <<>>; _ -> binary:part(Key, {0, Level}) end,
	KeySize = byte_size(Key),
	KeySuffix = case Key of <<>> -> <<>>; _ -> binary:part(Key, {Level, KeySize - Level}) end,
	case maps:get(KeyPrefix, Tree, not_found) of
		not_found ->
			not_found;
		{_, _, _, Suffix, MaybeValue} ->
			Len = binary:longest_common_prefix([KeySuffix, Suffix]),
			SuffixSize = byte_size(Suffix),
			case Len < SuffixSize of
				true ->
					not_found;
				false ->
					case KeySuffix == Suffix of
						false ->
							get(Key, Tree, Level + SuffixSize + 1);
						true ->
							case MaybeValue of
								no_value ->
									get(Key, Tree, Level + SuffixSize);
								{v, Value} ->
									Value
							end
					end
			end
	end.

compute_hash(Tree, HashFun, Key) ->
	{Parent, Children, Hash, Suffix, MaybeValue} = maps:get(Key, Tree),
	case Hash of
		no_hash ->
			case Children of
				no_children ->
					{v, Value} = MaybeValue,
					NewHash = HashFun(Value),
					NewTree = Tree#{ Key => {Parent, no_children, NewHash, Suffix, {v, Value}} },
					{NewHash, NewTree};
				_ ->
					{Hashes, UpdatedTree} = gb_sets_foldr(
						fun(Child, {HashesAcc, TreeAcc}) ->
							{ChildHash, TreeAcc2} = compute_hash(TreeAcc, HashFun, Child),
							{[ChildHash | HashesAcc], TreeAcc2}
						end,
						{[], Tree},
						Children
					),
					NewHash = ar_deep_hash:hash(
						case MaybeValue of
							{v, Value} ->
								[HashFun(Value) | Hashes];
							no_value ->
								Hashes
						end
					),
					{NewHash, UpdatedTree#{
						Key => {Parent, Children, NewHash, Suffix, MaybeValue}
					}}
			end;
		_ ->
			{Hash, Tree}
	end.

foldr(Fun, Acc, Tree, Key) ->
	{_, Children, _, _, MaybeValue} = maps:get(Key, Tree),
	case Children of
		no_children ->
			{v, Value} = MaybeValue,
			Fun(Value, Acc);
		_ ->
			Acc2 = gb_sets_foldr(
				fun(Child, ChildrenAcc) ->
					foldr(Fun, ChildrenAcc, Tree, Child)
				end,
				Acc,
				Children
			),
			case MaybeValue of
				{v, Value} ->
					Fun(Value, Acc2);
				_ ->
					Acc2
			end
	end.

gb_sets_foldr(Fun, Acc, G) ->
	case gb_sets:is_empty(G) of
		true ->
			Acc;
		false ->
			{Largest, G2} = gb_sets:take_largest(G),
			gb_sets_foldr(Fun, Fun(Largest, Acc), G2)
	end.

%%%===================================================================
%%% Tests.
%%%===================================================================

trie_test() ->
	T1 = new(),
	?assertEqual(not_found, get(<<"aaa">>, T1)),
	?assertEqual(true, is_empty(T1)),
	%% aaa -> 1
	T2 = insert(<<"aaa">>, 1, T1),
	?assertEqual(false, is_empty(T2)),
	{H2, T2_2} = compute_hash(T2, fun integer_to_binary/1),
	{H2_2, _} = compute_hash(T2_2, fun integer_to_binary/1),
	?assertEqual(H2, H2_2),
	?assertEqual(1, get(<<"aaa">>, T2)),
	%% aa -> a -> 1
	%%       b -> 2
	T3 = insert(<<"aab">>, 2, T2),
	{H3, _} = compute_hash(T3, fun integer_to_binary/1),
	?assertNotEqual(H2, H3),
	{H3_2, _} =
		compute_hash(
			insert(<<"aaa">>, 1, insert(<<"aab">>, 2, new())),
			fun integer_to_binary/1
		),
	?assertEqual(H3, H3_2),
	?assertEqual(1, get(<<"aaa">>, T3)),
	?assertEqual(2, get(<<"aab">>, T3)),
	T4 = insert(<<"aab">>, 3, T3),
	{H4, _} = compute_hash(T4, fun integer_to_binary/1),
	?assertNotEqual(H3, H4),
	?assertEqual(1, get(<<"aaa">>, T4)),
	?assertEqual(3, get(<<"aab">>, T4)),
	%% a -> a -> a -> 1
	%%           b -> 3
	%%      b -> 2
	T5 = insert(<<"ab">>, 2, T4),
	?assertEqual(1, gb_sets:size(element(2, maps:get(root, T5)))),
	{H5, _} = compute_hash(T5, fun integer_to_binary/1),
	?assertNotEqual(H4, H5),
	{H5_2, _} =
		compute_hash(
			insert(<<"aab">>, 3, insert(<<"aaa">>, 1, insert(<<"ab">>, 2, new()))),
			fun integer_to_binary/1
		),
	?assertEqual(H5, H5_2),
	{_H5_3, T5_2} = compute_hash(insert(<<"aaa">>, 1, new()), fun integer_to_binary/1),
	{_H5_4, T5_3} = compute_hash(insert(<<"ab">>, 2, T5_2), fun integer_to_binary/1),
	{H5_5, _T5_4} = compute_hash(insert(<<"aab">>, 3, T5_3), fun integer_to_binary/1),
	?assertEqual(H5, H5_5),
	?assertEqual(1, get(<<"aaa">>, T5)),
	?assertEqual(3, get(<<"aab">>, T5)),
	?assertEqual(2, get(<<"ab">>, T5)),
	%% a -> a -> a -> 1
	%%           b -> 3
	%%      b -> 2
	%%           c -> 4
	T6 = insert(<<"abc">>, 4, T5),
	?assertEqual(1, gb_sets:size(element(2, maps:get(root, T6)))),
	?assertEqual(1, get(<<"aaa">>, T6)),
	?assertEqual(3, get(<<"aab">>, T6)),
	?assertEqual(2, get(<<"ab">>, T6)),
	?assertEqual(4, get(<<"abc">>, T6)),
	%% a -> a -> a -> 1
	%%           b -> 3
	%%      b -> 2
	%%           c -> 4
	%% bcdefj -> 4
	T7 = insert(<<"bcdefj">>, 4, T6),
	?assertEqual(2, gb_sets:size(element(2, maps:get(root, T7)))),
	?assertEqual(1, get(<<"aaa">>, T7)),
	?assertEqual(3, get(<<"aab">>, T7)),
	?assertEqual(4, get(<<"abc">>, T7)),
	?assertEqual(4, get(<<"bcdefj">>, T7)),
	%% a -> a -> a -> 1
	%%           b -> 3
	%%      b -> 2
	%%           c -> 4
	%% bcd -> efj -> 4
	%%        bcd -> 5
	T8 = insert(<<"bcdbcd">>, 5, T7),
	?assertEqual(4, get(<<"bcdefj">>, T8)),
	?assertEqual(5, get(<<"bcdbcd">>, T8)),
	T9 = insert(<<"bcdbcd">>, 6, T8),
	?assertEqual(4, get(<<"bcdefj">>, T9)),
	?assertEqual(6, get(<<"bcdbcd">>, T9)),
	%% a -> a -> a -> 1
	%%           b -> 3
	%%      b -> 2
	%%           c -> 4
	%% bab -> 7
	%% bcd -> efj -> 4
	%%        bcd -> 6
	T10 = insert(<<"bab">>, 7, T9),
	?assertEqual(1, get(<<"aaa">>, T10)),
	?assertEqual(3, get(<<"aab">>, T10)),
	?assertEqual(4, get(<<"abc">>, T10)),
	?assertEqual(4, get(<<"bcdefj">>, T10)),
	?assertEqual(4, get(<<"bcdefj">>, T10)),
	?assertEqual(6, get(<<"bcdbcd">>, T10)),
	?assertEqual(7, get(<<"bab">>, T10)),
	%% a -> a -> a -> 1
	%%           b -> 3
	%%      b -> 2
	%%           c -> 4
	%% b -> a -> b -> 7
	%%      a -> a -> 8
	%% bcd -> efj -> 4
	%%        bcd -> 6
	T11 = insert(<<"baa">>, 8, T10),
	?assertEqual(1, get(<<"aaa">>, T11)),
	?assertEqual(3, get(<<"aab">>, T11)),
	?assertEqual(4, get(<<"abc">>, T11)),
	?assertEqual(4, get(<<"bcdefj">>, T11)),
	?assertEqual(4, get(<<"bcdefj">>, T11)),
	?assertEqual(6, get(<<"bcdbcd">>, T11)),
	?assertEqual(7, get(<<"bab">>, T11)),
	?assertEqual(8, get(<<"baa">>, T11)),
	%% a -> a -> a -> 1
	%%           b -> 3
	%%      b -> 2
	%%           c -> 4
	%% b -> a -> b -> 7
	%%      a -> a -> 8
	%% bcd -> efj -> 4
	%%        bcd -> 6
	%% <<>> -> empty
	T12 = insert(<<>>, empty, T11),
	?assertEqual(1, get(<<"aaa">>, T12)),
	?assertEqual(3, get(<<"aab">>, T12)),
	?assertEqual(4, get(<<"abc">>, T12)),
	?assertEqual(4, get(<<"bcdefj">>, T12)),
	?assertEqual(4, get(<<"bcdefj">>, T12)),
	?assertEqual(6, get(<<"bcdbcd">>, T12)),
	?assertEqual(7, get(<<"bab">>, T12)),
	?assertEqual(8, get(<<"baa">>, T12)),
	?assertEqual(empty, get(<<>>, T12)),
	?assertEqual(
		[empty, 1, 3, 2, 4, 8, 7, 6, 4],
		foldr(fun(El, Acc) -> [El | Acc] end, [], T12)
	),
	{H12, _} = compute_hash(T12, fun term_to_binary/1),
	T13 = from_proplist([
		{<<"bcdbcd">>, 6},
		{<<>>, empty},
		{<<"ab">>, 2},
		{<<"baa">>, 8},
		{<<"aab">>, 3},
		{<<"bab">>, 7},
		{<<"aaa">>, 1},
		{<<"abc">>, 4},
		{<<"bcdefj">>, 4}
	]),
	{H13, _} = compute_hash(T13, fun term_to_binary/1),
	?assertEqual(H12, H13),
	?assertEqual(1, get(<<"aaa">>, T13)),
	?assertEqual(3, get(<<"aab">>, T13)),
	?assertEqual(4, get(<<"abc">>, T13)),
	?assertEqual(4, get(<<"bcdefj">>, T13)),
	?assertEqual(4, get(<<"bcdefj">>, T13)),
	?assertEqual(6, get(<<"bcdbcd">>, T13)),
	?assertEqual(7, get(<<"bab">>, T13)),
	?assertEqual(8, get(<<"baa">>, T13)),
	?assertEqual(empty, get(<<>>, T13)),
	%% a -> a -> a -> 1
	%%           b -> 3
	%%      b -> 2
	%%           c -> 4
	%% b -> a -> b -> 7
	%%      a -> a -> 8
	%% bcd -> efj -> 4
	%%        bc -> 9
	%%              d -> 6
	%% <<>> -> empty
	T14 = insert(<<"bcdbc">>, 9, T13),
	?assertEqual(1, get(<<"aaa">>, T14)),
	?assertEqual(3, get(<<"aab">>, T14)),
	?assertEqual(4, get(<<"abc">>, T14)),
	?assertEqual(4, get(<<"bcdefj">>, T14)),
	?assertEqual(4, get(<<"bcdefj">>, T14)),
	?assertEqual(6, get(<<"bcdbcd">>, T14)),
	?assertEqual(7, get(<<"bab">>, T14)),
	?assertEqual(8, get(<<"baa">>, T14)),
	?assertEqual(9, get(<<"bcdbc">>, T14)),
	?assertEqual(empty, get(<<>>, T14)),
	T15 = insert(<<"bcdbc">>, 10, T14),
	?assertEqual(10, get(<<"bcdbc">>, T15)),
	?assertEqual(6, get(<<"bcdbcd">>, T15)).
