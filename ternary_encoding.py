import itertools

import time
import math
from pysmt.shortcuts import Symbol, And, Or, Plus, Int, Equals, get_model, BV
from pysmt.shortcuts import Solver, reset_env, ForAll
from pysmt.typing import INT, BVType, ArrayType, BOOL
from pysmt.logics import LIA, LRA

problems = [
    (3, 2, 5),
    (4, 3, 10),
    (5, 4, 20),
    (6, 4, 40)
]
for NB, NT, K in problems:
    env = reset_env()
    env.enable_infix_notation = True

    start_time = time.time()

    #NB = 3
    #NT = 2
    #K = 5
    #NB = 11
    #NT = 7
    #K = 128

    num_parents = NB + K
    index_width = math.ceil(math.log2(num_parents))
    INDEX = BVType(index_width)
    Index = lambda x: BV(x, width=index_width)
    def index_constraint(sym):
        return sym <= Index(num_parents-1)

    COPIEDBIT = BVType(width=2**NB)
    CopiedBit = lambda x: BV(x, width=2**NB)

    #TRIT = BVType(width=2)
    COPIEDTRITPIECE = BVType(2**NB)
    CopiedTritPiece_const0 = BV(0, width=2**NB)
    def trit_to_str(tx, ty):
        zero = BV(0, width=1)
        one = BV(1, width=1)
        if tx == zero and ty == zero:
            return 'A'
        if tx == zero and ty == one:
            return 'B'
        if tx == one and ty == zero:
            return 'C'
        if tx == one and ty == one:
            return 'X'

    STYLE = BVType(1)
    Style = lambda x: BV(x, width=1)
    NOR_GATE = Style(0)
    NAND_GATE = Style(1)
    styles = ['NOR', 'NAND']
    #NULL_GATE = Style(2)

    parent_lookup_type = ArrayType(INDEX, COPIEDBIT)
    parent_lookup = Symbol("parent_lookup", parent_lookup_type)

    all_binary_codes = list(itertools.product([0, 1], repeat=NB))
    for input_bit_i in range(NB):
        copies_of_bit = [c[input_bit_i] for c in all_binary_codes]
        #bit_values_const = copied_bit_type(copies_of_bit)
        copies_str = ''.join(str(x) for x in copies_of_bit)
        bit_values_const = CopiedBit(copies_str)
        parent_lookup = parent_lookup.Store(Index(input_bit_i), bit_values_const)
        #print('stored',Index(input_bit_i), bit_values_const )

    for gate_num in range(K):
        gate_result = Symbol(f'gate_{gate_num}_result', COPIEDBIT)
        parent_lookup.Store(Index(NB+gate_num), gate_result)

    def make_gate(number):
        name = f"gate_{number}"
        parent_a_i = Symbol(f'{name}_parent_a_i', INDEX)
        parent_b_i = Symbol(f'{name}_parent_b_i', INDEX)
        parent_a = parent_lookup.Select(parent_a_i)
        parent_b = parent_lookup.Select(parent_b_i)

        # TODO this doesn't need to be a select because the index is constant; hopefully it's smart enough to optimize
        gate_result = parent_lookup.Select(Index(NB+number))

        # note we go stricter than the index_constraint to prevent combinational loops
        gate_style = Symbol(f'{name}_style', STYLE)
        constraint = And([
            Or([
                And([Equals(gate_style, NOR_GATE),  Equals(gate_result, ~ (parent_a | parent_b))]),
                And([Equals(gate_style, NAND_GATE), Equals(gate_result, ~ (parent_a & parent_b))]),
                #And([Equals(gate_style, NULL_GATE), ])
            ]),
            And([
                #index_constraint(parent_a_i),
                #index_constraint(parent_b_i)
                parent_a_i <= NB + number - 1,
                parent_b_i <= NB + number - 1,
            ])
        ])

        symbols = (parent_a_i, parent_b_i, parent_a, parent_b, gate_style, gate_result)
        return constraint, symbols

    rules = []
    gates = []
    for gate_num in range(K):
        constraint, gate = make_gate(gate_num)
        rules.append(constraint)
        gates.append(gate)

    trit_values = []
    def make_trit(number):
        name = f"trit_{number}"
        # 2 parents because we represent the trit with 2 bits
        parent_x_i = Symbol(f'{name}_parent_x_i', INDEX)
        parent_y_i = Symbol(f'{name}_parent_y_i', INDEX)
        parent_x = parent_lookup.Select(parent_x_i)
        parent_y = parent_lookup.Select(parent_y_i)

        value_x = Symbol(f'{name}_valx', COPIEDTRITPIECE)
        value_y = Symbol(f'{name}_valy', COPIEDTRITPIECE)
        trit_values.append((value_x, value_y))

        # third constraint constrains only (0,0), (0,1), (1,0) for the 3 trit values
        constraint = And([
            index_constraint(parent_x_i),
            index_constraint(parent_y_i),
            Equals(value_x, parent_x),
            Equals(value_y, parent_y),
            Equals(value_x & value_y, CopiedTritPiece_const0)
        ])

        # TODO add constraint for not equaling 11

        symbols = (parent_x_i, parent_y_i, parent_x, parent_y, value_x, value_y)
        return constraint, symbols

    trits = []
    for trit_num in range(NT):
        constraint, trit = make_trit(trit_num)
        trits.append(trit)
        rules.append(constraint)


    print('before uniqueness', time.time() - start_time)


    uniqueness_rules = []

    '''
    # original, with explicit matchups
    for input_code_i, input_code_j in itertools.combinations(range(2**NB), r=2):
        # ternary output can't match completely between these two codes
        piecewise_matchup = []
        for trit_k in range(NT-1, -1, -1):
            tkx = trit_values[trit_k][0]
            tky = trit_values[trit_k][1]
            piecewise_matchup.append((tkx[input_code_i], tkx[input_code_j]))
            piecewise_matchup.append((tky[input_code_i], tky[input_code_j]))
        uniqueness_rule = Or([~Equals(piece_i, piece_j) for piece_i, piece_j in piecewise_matchup])
        uniqueness_rules.append(uniqueness_rule)
    '''

    '''
    BROKEN
    all_index_width = math.ceil(math.log2(3**NT))
    ALL_INDEX = BVType(all_index_width)
    AllIndex = lambda x: BV(x, width=all_index_width)
    all_type = ArrayType(ALL_INDEX, BVType(NT))
    all_ternary_arrayx = Symbol('all_arrayx', all_type)
    all_ternary_arrayy = Symbol('all_arrayy', all_type)
    # TODO is this ald comment wrong? fill an array length 3**NT with chosen trit values plus new symbols
    for i in range(2**NB):
        tx_sel = Symbol(f'tritx_{i}_selected', BVType(NT))
        ty_sel = Symbol(f'trity_{i}_selected', BVType(NT))
        for j, (tx, ty) in enumerate(trit_values):
            uniqueness_rules.append(Equals(tx_sel[j], tx[i]))
            uniqueness_rules.append(Equals(ty_sel[j], ty[i]))
        all_ternary_arrayx = all_ternary_arrayx.Store(AllIndex(i), tx_sel)
        all_ternary_arrayy = all_ternary_arrayy.Store(AllIndex(i), ty_sel)
    for i in range(len(trit_values), 3**NT):
        all_ternary_arrayx = all_ternary_arrayx.Store(AllIndex(i), Symbol(f'unused_trit_valuex_{i}', BVType(NT)))
        all_ternary_arrayy = all_ternary_arrayy.Store(AllIndex(i), Symbol(f'unused_trit_valuey_{i}', BVType(NT)))
    for ternary_value in itertools.product(range(3), repeat=NT):
        tx_literal = ''.join('0' if t in [0, 1] else '1' for t in ternary_value)
        ty_literal = ''.join('0' if t in [0, 2] else '1' for t in ternary_value)
        all_index = Symbol(f'all_index_{i}', ALL_INDEX)
        uniqueness_rules.append(Equals(all_ternary_arrayx.Select(all_index), BV(tx_literal, width=NT)))
        #uniqueness_rules.append(Equals(all_ternary_arrayy.Select(all_index), BV(ty_literal, width=NT)))
    rules.append(And(uniqueness_rules))
    '''

    '''
    # using arrays to match up a ternary string with every binary string
    # make an array witn 3^NT entries
    # each entry gets a free variable
    # for each ternary string, assert that the entry at that index equals its binary string
    all_index_width = 2*NT
    ALL_INDEX = BVType(all_index_width)
    AllIndex = lambda x: BV(x, width=all_index_width)
    all_type = ArrayType(ALL_INDEX, BVType(NB))
    all_array = Symbol('all_arrayx', all_type)
    for i in range(2**NB):
        index = Symbol(f't{i}_rearranged', ALL_INDEX)
        for j, (tx, ty) in enumerate(trit_values):
            uniqueness_rules.append(Equals(index[2*j+0], tx[i]))
            uniqueness_rules.append(Equals(index[2*j+1], ty[i]))
        unique_code = BV(''.join(str(x) for x in all_binary_codes[i]), width=NB)
        uniqueness_rules.append(Equals(all_array.Select(index), unique_code))
    '''

    # using ForAll
    # pack each ternary sequence into an array
    array = Symbol('ternary_lookup_array', ArrayType(INDEX, BVType(2*NT)))
    for binary_seq_id in range(2**NB):
        ternary_seq = Symbol(f'ternary_seq_{binary_seq_id}', BVType(2*NT))
        array = array.Store(BV(binary_seq_id, width=NB), ternary_seq)
        for trit_i in range(NT):
            for trit_piece in [0, 1]:
                uniqueness_rules.append(Equals(ternary_seq[2*trit_i+trit_piece],
                                               trit_values[trit_i][trit_piece][binary_seq_id]
                                               ))
    index_i = Symbol('index_i', INDEX)
    index_j = Symbol('index_j', INDEX)
    #f = ForAll([index_i, index_j], And([
    #    ~Equals(trit_values[trit_i][trit_piece][index_i], trit_values[trit_i][trit_piece][index_j])
    #    for trit_piece in [0,1]
    #    for trit_i in range(NT)
    #])
    #           )
    f = ForAll([index_i, index_j], ~Equals(array.Select(index_i), array.Select(index_j)))
    uniqueness_rules.append(f)



    rules.append(And(uniqueness_rules))



    #print('uniqueness:', uniqueness_rules)

    rule = And(rules)


    def name_parent(index):
        index = index.constant_value()
        if index < NB:
            return f'bit_{index} ({index})'
        else:
            return f'gate_{index - NB} ({index})'

    print('about to solve', time.time() - start_time)
    #model = get_model(rule, solver_name='z3', logic=LRA)

    #
    with Solver(name='cvc4', logic=LRA) as s:
        s.add_assertion(f)
        res = s.solve()
        self.assertTrue(res)
        exit()


    model = get_model(rule, solver_name='cvc4')
    if model:
        '''
        #print(model)
        for gate_i, gate in enumerate(gates):
            parent_a_i, parent_b_i, parent_a, parent_b, gate_style, gate_result = gate
            pai = model.get_value(parent_a_i)
            pbi = model.get_value(parent_b_i)
            pa = model.get_value(parent_a)
            pb = model.get_value(parent_b)
            r = model.get_value(gate_result)
            s = model.get_value(gate_style)

            print(f'\nGate {gate_i}')
            print(f'Parents: {name_parent(pai)}, {name_parent(pbi)}')
            print(f'Parent values: {pa}, {pb}')
            print(f'Style: {styles[s.constant_value()]}, Result: {r}')
        print()

        '''

        trit_values = []
        trit_parents = []
        for trit_i, trit in enumerate(trits):
            parent_x_i, parent_y_i, parent_x, parent_y, value_x, value_y = trit
            pxi = model.get_value(parent_x_i)
            pyi = model.get_value(parent_y_i)
            px = model.get_value(parent_x)
            py = model.get_value(parent_y)
            vx = model.get_value(value_x)
            vy = model.get_value(value_y)

            trit_values.append((vx, vy))

            print(f'\nTernary {trit_i}')
            print(f'Parents: {name_parent(pxi)}, {name_parent(pyi)}')
            print(f'Parent values: {px}, {py}')
        print()

        for i, binary_code in enumerate(all_binary_codes):
            ts = []
            for j in range(NT):
                tx = trit_values[j][0][i].simplify()
                ty = trit_values[j][1][i].simplify()
                ts.append((trit_to_str(tx, ty), (tx, ty)))

            print(binary_code, *ts)


    else:
        print('couldnt find a mapping')
        #print(model)

    print(f'{NB}, {NT}, {K} done', time.time() - start_time)


    break
    print()


'''
Original uniqueness rule took 2668 seconds to define, then ran out of memory while solving
New uniqueness took 1.25 seconds LOL but still no news when I stopped it after 6 hours



With z3 and old uniqueness:
3,2,5 takes 0.3
4,3,10 takes 4.16
5,4,20 takes 407.4

With z3 and new uniqueness:
3,2,5 takes .2
4,3,10 takes 5.39
5,4,20 takes 171.7
'''