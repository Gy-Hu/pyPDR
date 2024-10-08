'''
The parser for PDR
'''
import re
from z3 import *

from pdr import * #marked
from solver import TCube
class Header:
    def __init__(self, max_idx: int, nIn: int, nLatch: int, nOut: int, nAnd: int, nBad: int, nInvariant):
        self.max_var_index = max_idx
        self.inputs = nIn
        self.latches = nLatch
        self.outputs = nOut
        self.ands = nAnd
        self.bads = nBad
        self.invariants = nInvariant


class Latch:
    def __init__(self, _var: str, _next: str, _init: str):
        self.var = _var
        self.next = _next
        self.init = _init

    def __repr__(self):
        return str(self.var) + ", " \
               + str(self.next) + ", " \
               + str(self.init)


class AND:
    def __init__(self, _lhs: str, _rhs0: str, _rhs1: str):
        self.lhs = _lhs
        self.rhs0 = _rhs0
        self.rhs1 = _rhs1

    def __repr__(self):
        return str(self.lhs) + ", " \
               + str(self.rhs0) + ", " \
               + str(self.rhs1)


def read_in(fileName: str):
    '''
    :param fileName:
    :return: inputs, latches, outputs, ands, bads, invariants, annotations
    '''
    inputs = list()
    outputs = list()
    bads = list()
    latches = list()
    ands = list()
    invariants = list()
    annotations = list()

    HEADER_PATTERN = re.compile("aag (\d+) (\d+) (\d+) (\d+) (\d+)(?: (\d+))?(?: (\d+))?\n")
    IO_PATTERN = re.compile("(\d+)\n")
    LATCH_PATTERN = re.compile("(\d+) (\d+)(?: (\d+))?\n")
    AND_PATTERN = re.compile("(\d+) (\d+) (\d+)\n")
    ANNOTATION_PATTERN = re.compile("\S+ (\S+)\n")

    with open(fileName, 'r') as f:
        head_line = f.readline()
        cont = re.match(HEADER_PATTERN, head_line)
        if cont is None:
            print("Don't support constraint, fairness, justice property yet")
            exit(1)

        header = Header(
            int(cont.group(1)),
            int(cont.group(2)),
            int(cont.group(3)),
            int(cont.group(4)),
            int(cont.group(5)),
            int(cont.group(6)) if cont.group(6) is not None else 0,
            int(cont.group(7)) if cont.group(7) is not None else 0
        )

        input_num = header.inputs
        output_num = header.outputs
        bad_num = header.bads
        latch_num = header.latches
        and_num = header.ands
        invariant_num = header.invariants

        for line in f.readlines():
            if input_num > 0:
                h = re.match(IO_PATTERN, line)
                if h:
                    # print("input node")
                    inputs.append(h.group(1))
                    # print(str(h.group(1)))
                    input_num -= 1
            elif latch_num > 0:
                h = re.match(LATCH_PATTERN, line)
                if h:
                    # print("latches node")
                    if h.group(3) is None:
                        # print(h.groups())
                        latches.append(Latch(h.group(1), h.group(2), "0"))
                    else:
                        # print(h.groups())
                        latches.append(Latch(h.group(1), h.group(2), h.group(3)))
                    latch_num -= 1
            elif output_num > 0:
                h = re.match(IO_PATTERN, line)
                if h:
                    # print("output node")
                    outputs.append(h.group(1))
                    # print(str(h.group(1)))
                    output_num -= 1
            elif bad_num > 0:
                h = re.match(IO_PATTERN, line)
                if h:
                    # print("bad node")
                    bads.append(h.group(1))
                    # print(str(h.group(1)))
                    bad_num -= 1
            elif invariant_num > 0:
                h = re.match(IO_PATTERN, line)
                if h:
                    # print("invariant node")
                    invariants.append(h.group(1))
                    # print(str(h.group(1)))
                    invariant_num -= 1
            elif and_num > 0:
                h = re.match(AND_PATTERN, line)
                if h:
                    # print("and node")
                    # print(str(h.groups()))
                    ands.append(AND(h.group(1), h.group(2), h.group(3)))
                    and_num -= 1 
                    #TODO: 现在需要dataset里面aag文件最后有一个空行，实际上这部分代码是有点问题的
            else:
                h = re.match(ANNOTATION_PATTERN, line)
                if h:
                    annotations.append(h.group(1))
        return inputs, latches, outputs, ands, bads, invariants, annotations


class Model:
    def __init__(self):
        self.inputs = []
        self.vars = []
        self.primed_vars = []
        self.inp_prime = []
        self.innards = []
        self.trans = tCube()
        self.init = tCube()
        self.post = tCube()
        #internal_signals_mapping = tCube()
        self.pv2next = dict()
        self.inp_prime = []
        self.filename = ''
        #self.latch_to_innards = {}
        #self.implicant_table = {}
        #self.logic_internal_connections = {}
        internal_signals_mapping = {}
        
    # def is_valid_expression(self, expr):
    #     """
    #     Check if the expression is of the form And(Not(v1), Not(v2)) or And(v1, v2).
    #     """
    #     if expr.decl().kind() == And().decl().kind():
    #         children = expr.children()
    #         if len(children) == 2:
    #             left_child, right_child = children
    #             # situation 1: !v1 && !v2 -> left_child = Not(v1), right_child = Not(v2), -> v1, v2 in self.vars
    #             if len(left_child.children()) == 1 and len(right_child.children()) == 1: # fulfill the Not conditions
    #                 return left_child.children()[0] in self.vars and right_child.children()[0] in self.vars
    #             # situation 2: v1 && v2 -> left_child = v1, right_child = v2, -> v1, v2 in self.vars
    #             elif left_child in self.vars and right_child in self.vars:
    #                 return True
    #             # situation 3: !v1 && v2 -> left_child = Not(v1), right_child = v2, -> v1, v2 in self.vars
    #             elif len(left_child.children()) == 1 and len(right_child.children()) == 1: # fulfill the Not conditions
    #                 return left_child.children()[0] in self.vars
    #             # situation 4: v1 && !v2 -> left_child = v1, right_child = Not(v2), -> v1, v2 in self.vars
    #             elif left_child in self.vars and len(right_child.children()) == 1:
    #                 return right_child.children()[0] in self.vars
    #     return False
        
    # def generate_implicant_propagation_table(self):
    #     implicant_table = {}

    #     for key, value in self.logic_internal_connections.items():
    #         if value.decl().kind() == And().decl().kind():
    #             children = value.children()
    #             if len(children) == 2:
    #                 left_child, right_child = children

    #                 if len(left_child.children()) == 1 and len(right_child.children()) == 1:
    #                     # situation 1: !v1 && !v2
    #                     v1, v2 = left_child.children()[0], right_child.children()[0]
    #                     self.add_implicant_relation(implicant_table, Bool(str(v1)) == True, [(Bool(str(v2)) == True, Bool(str(v2)) == False)])
    #                     self.add_implicant_relation(implicant_table, Bool(str(v2)) == True, [(Bool(str(v1)) == True, Bool(str(v1)) == False)])
    #                 elif left_child in self.vars and right_child in self.vars:
    #                     # situation 2: v1 && v2
    #                     v1, v2 = left_child, right_child
    #                     self.add_implicant_relation(implicant_table, Bool(str(v1)) == False, [(Bool(str(v2)) == False, Bool(str(v2)) == True)])
    #                     self.add_implicant_relation(implicant_table, Bool(str(v2)) == False, [(Bool(str(v1)) == False, Bool(str(v1)) == True)])
    #                 elif len(left_child.children()) == 1:
    #                     # situation 3: !v1 && v2
    #                     v1, v2 = left_child.children()[0], right_child
    #                     self.add_implicant_relation(implicant_table, Bool(str(v1)) == True, [(Bool(str(v2)) == False, Bool(str(v2)) == True)])
    #                     self.add_implicant_relation(implicant_table, Bool(str(v2)) == False, [(Bool(str(v1)) == True, Bool(str(v1)) == False)])
    #                 elif len(right_child.children()) == 1:
    #                     # situation 4: v1 && !v2
    #                     v1, v2 = left_child, right_child.children()[0]
    #                     self.add_implicant_relation(implicant_table, Bool(str(v1)) == False, [(Bool(str(v2)) == True, Bool(str(v2)) == False)])
    #                     self.add_implicant_relation(implicant_table, Bool(str(v2)) == True, [(Bool(str(v1)) == False, Bool(str(v1)) == True)])

    #     return implicant_table

    def add_implicant_relation(self, table, key, implications):
        if key not in table:
            table[key] = []
        for implication in implications:
            if implication not in table[key]:
                table[key].append(implication)

    def parse(self, fileName, calc_latch_to_innards=True, calc_implicant_table=True):
        '''
        :param fileName:
        :return:
        '''
        self.filename = fileName
        i, l, o, a, b, c, annotations = read_in(fileName)

        ann_i = 0
        # input node
        inp = dict()
        self.inputs = list()
        for it in i:
            if ann_i < len(annotations):
                name = "i" + it + "[" + annotations[ann_i] + "]"
            else:
                name = "i" + it
            ann_i += 1
            inp[it] = Bool(name)
            self.inputs.append(inp[it])

        # input'
        pinp = dict()
        self.inp_prime = list()
        for it in i:
            #pinp[it] = Bool(str(inp[it]) + '\'') # v -> v'
            pinp[it] = Bool(str(inp[it]) + '_prime') # v -> v_prime, change this, because we want generate .smt2 later
            self.inp_prime.append(pinp[it])

        #print("inputs: ",self.inputs)

        # vars of latch
        vs = dict()
        self.vars = list()
        for it in l:
            # .... Original code
            if ann_i < len(annotations):
                name = "v" + it.var + "[" + annotations[ann_i] + "]"
            else:
                name = "v" + it.var
            ann_i += 1
            vs[it.var] = Bool(name)
            self.vars.append(vs[it.var])
            
        

        # vars' of latch
        pvs = dict()
        self.primed_vars = list()
        for it in l:
            #pvs[it.var] = Bool(str(vs[it.var]) + '\'')
            pvs[it.var] = Bool(str(vs[it.var]) + '_prime') # v -> v_prime, change this, because we want generate .smt2 later
            self.primed_vars.append(pvs[it.var])

        # and gate node => And(and1, and2)
        ands = dict()
        for it in a:
            rs0 = True
            rs1 = True
            if it.rhs0 == "1":
                rs0 = True
            elif it.rhs0 == "0":
                rs0 = False
            elif int(it.rhs0) & 1 != 0:
                v = str(int(it.rhs0) - 1)
                if v in inp.keys():
                    rs0 = Not(inp[v])
                elif v in vs.keys():
                    rs0 = Not(vs[v])
                elif v in ands.keys():
                    rs0 = Not(ands[v])
                else:
                    print("Error in AND definition, in node " + v)
                    exit(1)
            else:
                v = it.rhs0
                if v in inp.keys():
                    rs0 = inp[v]
                elif v in vs.keys():
                    rs0 = vs[v]
                elif v in ands.keys():
                    rs0 = ands[v]
                else:
                    print("Error in AND definition, in node " + v)
                    exit(1)

            if it.rhs1 == "1":
                rs1 = True
            elif it.rhs1 == "0":
                rs1 = False
            elif int(it.rhs1) & 1 != 0:
                v = str(int(it.rhs1) - 1)
                if v in inp.keys():
                    rs1 = Not(inp[v])
                elif v in vs.keys():
                    rs1 = Not(vs[v])
                elif v in ands.keys():
                    rs1 = Not(ands[v])
                else:
                    print("Error in AND definition, in node " + v)
                    exit(1)
            else:
                v = it.rhs1
                if v in inp.keys():
                    rs1 = inp[v] # input
                elif v in vs.keys():
                    rs1 = vs[v] # vars of latch (in dict)
                elif v in ands.keys():
                    rs1 = ands[v]
                else:
                    print("Error in AND definition, in node " + v)
                    exit(1)

            ands[it.lhs] = And(rs0, rs1)
        
        
            
        # Create the internal_signals dictionary
        internal_signals_mapping = {f"innards_{i}": expr for i, (lhs, expr) in enumerate(ands.items())}
        
        # add the innards into list, just like self.init
        for k, v in internal_signals_mapping.items():
            self.innards.append(Bool(k))
        # make internal signal to tCube
        #internal_signals_mapping.addAnds([v for v in ands.values()])
            
        # if calc_latch_to_innards:
        #     # latch_to_innards    
        #     for it in l:
        #         # Create the latch_to_innards mapping
        #         latch = vs[it.var]
        #         self.latch_to_innards[latch] = []
        #         if it.next != "0" and it.next != "1":
        #             v = it.next if int(it.next) & 1 == 0 else str(int(it.next) - 1)
        #             if v in ands.keys():
        #                 self.latch_to_innards[latch].append(ands[v])

        # initial condition, init = And(inits{Bool(latch_node)})
        inits_var = list()
        for it in l:
            if it.init == "0":
                inits_var.append(Not(vs[it.var]))
            elif it.init == "1":
                inits_var.append(vs[it.var])
        self.init.addAnds(inits_var)

        # transition. trans_items: asserts.
        trans_items = list()
        for it in l:
            if it.next == "1":
                trans_items.append(pvs[it.var] == And(True))
                self.pv2next[pvs[it.var]] = And(True)
            elif it.next == "0":
                trans_items.append(pvs[it.var] == And(False))
                self.pv2next[pvs[it.var]] = And(False)
            elif int(it.next) & 1 == 0:
                v = it.next
                if v in inp.keys():
                    trans_items.append(pvs[it.var] == inp[v])
                    self.pv2next[pvs[it.var]] = inp[v]
                elif v in vs.keys():
                    trans_items.append(pvs[it.var] == vs[v])
                    self.pv2next[pvs[it.var]] = vs[v]
                elif v in ands.keys():
                    trans_items.append(pvs[it.var] == ands[v])
                    self.pv2next[pvs[it.var]] = ands[v]
                else:
                    print("Error in transition relation")
                    exit(1)
            else:
                v = str(int(it.next) - 1)
                if v in inp.keys():
                    trans_items.append(pvs[it.var] == Not(inp[v]))
                    self.pv2next[pvs[it.var]] = Not(inp[v])
                elif v in vs.keys():
                    trans_items.append(pvs[it.var] == Not(vs[v]))
                    self.pv2next[pvs[it.var]] = Not(vs[v])
                elif v in ands.keys():
                    trans_items.append(pvs[it.var] == Not(ands[v]))
                    self.pv2next[pvs[it.var]] = Not(ands[v])
                else:
                    print("Error in transition relation")
                    exit(1)
        self.trans.addAnds(trans_items)

        #print("trans:",self.trans.cube())
        # print(self.trans.cube())

        # postulate
        property_items = list()
        # bads
        #for it in b:
        for it in o: #output as bad state
            tmp = int(it)
            if tmp & 1 == 0:
                if it in inp.keys():
                    property_items.append(Not(inp[it]))
                elif it in vs.keys():
                    property_items.append(Not(vs[it]))
                elif it in ands.keys():
                    property_items.append(Not(ands[it]))
                else:
                    print("Error in property definition")
                    exit(1)
            else:
                it = str(int(it) - 1)
                if it in inp.keys():
                    property_items.append(inp[it])
                elif it in vs.keys():
                    property_items.append(vs[it])
                elif it in ands.keys():
                    property_items.append(ands[it])
                else:
                    print("Error in property definition")
                    exit(1)
        # invariants
        # for it in c:
        #     tmp = int(it)
        #     if tmp & 1 == 0:
        #         if it in inp.keys():
        #             property_items.append(inp[it])
        #         elif it in vs.keys():
        #             property_items.append(vs[it])
        #         elif it in ands.keys():
        #             property_items.append(ands[it])
        #         else:
        #             print("Error in property definition")
        #             exit(1)
        #     else:
        #         it = str(int(it) - 1)
        #         if it in inp.keys():
        #             property_items.append(Not(inp[it]))
        #         elif it in vs.keys():
        #             property_items.append(Not(vs[it]))
        #         elif it in ands.keys():
        #             property_items.append(Not(ands[it]))
        #         else:
        #             print("Error in property definition")
        #             exit(1)
        #print("postadd")
        #print("property items: ",property_items)
        self.post.addAnds(property_items) 
        #TODO: 修复这里识别不出bad state的问题，目前只有源文件btor用btor2tools转aiger的文件可以正常被parse
        # self.post.add(Or(vs['54'], vs['66'], Not(vs['68']), Not(vs['56'])))
        # print("postAdded")
        #print("self.inputs: ",self.inputs)
        #print("self.vars: ",self.vars)
        # if calc_implicant_table:
        #     # clone the ands into logic_internal_connections
        #     self.logic_internal_connections = ands.copy()
        #     # filtered_connections = {
        #     #     key: [connections if is_valid_expression(conn)]
        #     #     for key, connections in self.logic_internal_connections.items()
        #     # }

        #     for key, connections in self.logic_internal_connections.items():
        #         # Filter out the connections that get false in the is_valid_expression(connections)
        #         if not self.is_valid_expression(connections): # return False
        #             self.logic_internal_connections[key] = None
            
        #     self.logic_internal_connections = {k: v for k, v in self.logic_internal_connections.items() if v is not None}
            
            
        #     self.implicant_table = self.generate_implicant_propagation_table()
        
        # Update self.internal_connections with filtered connections
        #self.logic_internal_connections = filtered_connections       
        
        return self.inputs, self.vars, self.primed_vars, self.init, self.trans, self.post, self.pv2next, self.inp_prime, self.innards, internal_signals_mapping, self.filename


if __name__ == '__main__':
    pass
