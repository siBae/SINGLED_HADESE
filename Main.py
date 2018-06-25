'''
Created on April 25, 2018

@author: 1sooing@gmail.com
@version: 0.01
'''

# Hybrid Mode:
# HADESE offers hybrid execution modes - debugging mode and emulation mode.
#
# Debugging mode
# - done with IDA APIs.
# - Can be synchronized with the real CPU & disk state with codes.
# - Debugging mode enables all state changes of CPU and disk.
#
# Emulation
# - done with triton APIs.
# - Enables pre-exploring branches without real execution.
# - Enalbes us to expect the execution results.
#
#
#
# Operation
# - When landed securely on target APIs or symbolic branches, set up basecamp.
# - Execute until the basecamp using debugging mode.
# - After the basecamp, explore next basecamp using emulation.
# - While emulate, discovered branches about network traffic is recorded.
#
#
# Implementation Point
# - We should synchronize memory for alternatively using both debugging and emulation.
#       > We synchronize memory with highest priority on debugging exeucution.
#
# - to do this, we forces register and memory changes of every step-into operation using IDA callbacks.
#       > We should determine whether handle instruction before or after function calls.
#
# - When encountered kernel level return or operation, We just stop and explore branches.
#       > Use Pathfinding function to choose way to target branch. ( ex. EntryPoint to recv() )
#
# ref: funcap, pathfinder, ida-api, triton, ctf-scripts.
#

# IDA imports
import os
import sys
from idaapi import *
from idautils import *
from idc import *

# HADESE internal imports
from triton import *

# Configuration Settings
Debug_Level = 2


'''
Script option
'''
# Block Color
COLOR_ASSEM = 0xA0A0FF
COLOR_BLOCK = 0x70E01B

# Memory mapping to essential APIs
# USER_DEFINED_API = ['socket', 'connect', 'bind', 'recv', 'send']
# USER_DEFINED_API = ['recv', 'send']
USER_DEFINED_API = ['recv']
# USER_DEFINED_API = ['socket']
USER_DEFINED_ADDR = []

GOOD_BRANCH = {}


'''
Path data structure
1. path [path][function][block] -> selected
2. path [path][function][block][instruction] -> not necessary

[ ex: path from main+0x77 to socket() ]
[0] [function 0]    [block 0] 
                    [block 1] -> socket()
    
    [function 1]    [block 0]   
                    [block 1]
    [function 2]    [block 0]
                    [block 1]
                    [block 2]
        ...
    [function 8]    [block 0]
                    [block 1]
                        ...
                    [block 5] -> main+0x77
[1] [function 0]    [block 0]
        ...
'''

ctx = TritonContext()
astCtxt = ctx.getAstContext()

regs = {
    'eax': REG.X86.EAX,
    'ebx': REG.X86.EBX,
    'ecx': REG.X86.ECX,
    'edx': REG.X86.EDX,
    'esi': REG.X86.ESI,
}


def symbolization_init():
    ctx.convertRegisterToSymbolicVariable(ctx.registers.eax)
    ctx.convertRegisterToSymbolicVariable(ctx.registers.ebx)
    ctx.convertRegisterToSymbolicVariable(ctx.registers.ecx)
    ctx.convertRegisterToSymbolicVariable(ctx.registers.edx)
    return


def emulate(Triton, pc):
    print '[+] Starting emulation.'
    while pc:
        # Fetch opcode
        #opcode = Triton.getConcreteMemoryAreaValue(pc, 16)
        opcode = GetManyBytes(pc, ItemSize(pc))  # Disassemble with IDA Pro

        # Create the Triton instruction
        instruction = Instruction()
        instruction.setOpcode(opcode)
        instruction.setAddress(pc)

        # Process
        Triton.processing(instruction)

        # print instruction

        for se in instruction.getSymbolicExpressions():
            se.setComment(str(instruction))

        # if instruction.mov:
        if str(instruction.getDisassembly()).split()[0] == 'mov':

            # for each operand, extract the address that esi points out
            # after extracted, we will symbolize the address
            for operand in instruction.getOperands():

                if operand.getType() == OPERAND.REG:

                    reg_type = str(operand).split(':')[0]
                    if reg_type == 'esi':
                        reg_ptr = ctx.getConcreteRegisterValue(operand)
                        ctx.convertRegisterToSymbolicVariable(
                            ctx.registers.esi)
                        print "\t'esi': " + hex(GetRegValue(reg_type))

                elif operand.getType() == OPERAND.MEM:
                    esi_ptr = operand.getBaseRegister()
                    reg_type_base = str(esi_ptr).split(':')[0]

                    if reg_type_base == 'esi':
                        # print "value: " + operand.getValue()
                        selection_starts = GetRegValue(reg_type)
                        selection_length = operand.getSize()
                        selection_ends = selection_starts + selection_length
                        ctx.convertMemoryToSymbolicVariable(
                            MemoryAccess(selection_starts, selection_length))
                        print "[+] Symbolizing memory from " + hex(selection_starts) + " to " + hex(selection_ends) + ". Total: " + str(selection_length) + " bytes"
                        # ctx.taintMemory(MemoryAccess(operand.getAddress(), operand.getSize()))
                        # print ("\t[esi]: " + str( GetManyBytes(operand.getAddress(), operand.getSize())) )

        # cmp validation check
        # 1. cmp is complicated
        # 2. cmp is comparing adjacive bytes of symbolized memory or recently
        # solved memory

        # decide whether MEM or REG
        # if MEM and symbolized
        # if REG and symbolized -> map a memory

        # after compare we handles jmp
        # in this case, we may need compare flag
        elif str(instruction.getDisassembly()).split()[0] == 'cmp':
            op = instruction.getOperands()[0]  # Get first operand
            reg_type = str(op).split(':')[0]

            if op.getType() == OPERAND.MEM:
                print("compare [" + str(GetManyBytes(op.getAddress(), op.getSize())
                                        ) + "] to " + str(instruction.getOperands()[1]).split(':')[0])
            elif op.getType() == OPERAND.REG:
                print("compare '" + hex(GetRegValue(reg_type)) + "' to " +
                      str(instruction.getOperands()[1]).split(':')[0])

        enable_step_trace(true)
        set_step_trace_options(0)

        # reg = instruction.getOperands()[0].isSymbolized() # Get first
        # operand

        #    if instruction.isConditionTaken():
        #        print 'branch will taken'
        #    else:
        #        print 'branch will not taken'
        #    break

        # negate & inject condition check
        # always print solution to check if solution is valid manually
        # elif instruction.isBranch():
        # Slice expressions
        # rax   = Triton.getSymbolicExpressionFromId(Triton.getSymbolicRegisterId(Triton.registers.esi))
        # eax   = astCtxt.extract(31, 0, rax.getAst())

        # Define constraint
        # cstr  = astCtxt.land([
        #             Triton.getPathConstraintsAst(),
        #             astCtxt.equal(eax, astCtxt.bv(1, 32))
        #         ])

        # print '[+] Asking for a model, please wait...'
        # model = Triton.getModel(cstr)
        # for k, v in model.items():
        #     value = v.getValue()
        #     Triton.setConcreteSymbolicVariableValue(Triton.getSymbolicVariableFromId(k), value)
        # print '[+] Symbolic variable %02d = %02x (%c)' %(k, value,
        # chr(value))

        # End of the CheckSolution() function
        if pc == 0x40ae90:
            print '[+] check point_1'
            break

            # Restart emulation with a good input.
            Triton = initialize()

        # Next
        #pc = Triton.getConcreteRegisterValue(Triton.registers.eip)
        pc = NextHead(pc)

    print '[+] Emulation done.'
    return

# utility functions


def format_name(ea):
    name = GetFunctionName(ea)
    if name == "" or name == None:
        name = "0x%x" % ea
    return name


def format_offset(ea):
    offset = GetFuncOffset(ea)
    if offset == "" or offset == None:
        offset = "0x%x" % ea
    return offset


def debug(message, level):
    ''' 
    Global Variables
    - level 0: Always displayed
    - level 1: Detailed information
    - level 2: More detailed debugging
    '''
    if level <= Debug_Level:
        print "[debug] " + message


class DbgImports():
    """
    DbgImports contains the names, ordinals and addresses of all imported functions as allocated at runtime.
    """

    def __init__(self):
        """
        Ctor
        """
        # self.logger = logging.getLogger(__name__)
        self.current_module_name = None

        # Real-Time import table
        # (Key -> Real func adrs.  Value -> (module_name, ea, name, ord)}
        self.rt_import_table = {}

    def getImportTableData(self):
        """
        Update rt_import_table with current import table data.
        """

        def imp_cb(ea, name, ord):
            """
            Import enumeration callback function. used by idaapi.enum_import_names .
            """

            tmpImports.append([self.current_module_name, ea, name, ord])
            return True

        # Contains static import table data (w\o real function addresses)
        tmpImports = []
        imp_num = idaapi.get_import_module_qty()  # Number of imported modules

        for i in xrange(0, imp_num):
            self.current_module_name = idaapi.get_import_module_name(i).lower()
            idaapi.enum_import_names(i, imp_cb)

        #  Get runtime function addresses and store in self.rt_import_table
        if not idaapi.is_debugger_on():
            raise RuntimeError("Debugger is not currently active.")

        for module_name, ea, name, ord in tmpImports:
            func_real_adrs = get_adrs_mem(ea)
            self.rt_import_table[func_real_adrs] = (module_name, ea, name, ord)

    def find_func_iat_adrs(self, ea):
        """
        Find the function location in the IAT table based on its runtime address
        @param ea: effective address of the function
        @return: a tuple of ('EA at the IAT' , 'Moudle Name')
        """
        if ea in self.rt_import_table:
            (module_name, iat_ea, name, ord) = self.rt_import_table[ea]
            return iat_ea, module_name

        return None, None

    def is_func_imported(self, ea):
        """
        Checks the given ea and returns True if the function is an imported function (loacted in IAT)
        """
        # If address is located in IAT
        if ea in self.rt_import_table:
            return True

        return False

    def is_func_module(self, ea, mod_name):
        """
        Check if function at ea is part of the imported module
        """
        if ea in self.rt_import_table:
            (module, ea, name, ord) = self.rt_import_table[ea]
            if module == mod_name:
                return True

        return False

    def is_loaded_module(self, module_name):
        """
        Check if module has loaded functions in the IAT
        @param module_name: Name of the module to search
        @return: True if model name is found in IAT, otherwise False
        """

        for (module, ea, name, ord) in self.rt_import_table.values():
            if module == module_name:
                return True
            return False

    def print_debug_imports(self):
        """
        Print the debug imports
        """
        for dbgImp in self.rt_import_table:
            (module_name, ea, name, ord) = self.rt_import_table[dbgImp]
            idaapi.msg("ModuleName - %s,\t\tFunctionName - %s,\t\t Address in IAT - %s,\t\t Real address - %s\n" %
                       (module_name, name, hex(ea), hex(dbgImp)))


def imp_callback(ea, name, ord):

    if not name:
        print "%08x: ordinal#%d" % (ea, ord)
    else:
        if name in USER_DEFINED_API:
            USER_DEFINED_ADDR.insert(0, ea)
            idc.SetColor(ea, idc.CIC_ITEM, COLOR_ASSEM)
            print "\tFound: %s [0x%x]" % (name, ea)
    # True -> Continue enumeration
    # False -> Stop enumeration
    return True


def explore_api():

    # Import address table
    nimps = idaapi.get_import_module_qty()
    print "Found %d import(s)..." % nimps

    for i in xrange(0, nimps):
        name = idaapi.get_import_module_name(i)
        if not name:
            print "Failed to get import module name for #%d" % i
            continue

        print "Walking-> %s" % name
        idaapi.enum_import_names(i, imp_callback)


def explore_path(src_ea, dst_ea):

    for xref in XrefsTo(dst_ea, 0):

        # real function(xref.frm) pointing idata function(ea)
        fnc_name = GetFunctionName(xref.frm)
        fnc_addr = LocByName(fnc_name)

        print "Finding Path from %s to %s" % (GetFunctionName(src_ea), fnc_name)
        # pathfinder = PathFinder(fnc_addr)
        pf = FunctionPathFinder(fnc_addr)
        results = pf.paths_from(src_ea)

        if not results:
            print "No possible path"
            continue

        print "[result]: %d" % len(results)
        # print results
        # for result in results:
        #     for res in result:
        #         print "\t[function] %s [0x%x]" % (GetFunctionName(res), res)

        # initialize cursor address
        cur_ea = fnc_addr
        cur_end = False

        while True:

            for xref in XrefsTo(cur_ea, 0):

                block_list = []
                pb_results = []

                # initialize function info
                function = idaapi.get_func(xref.frm)
                function_name = GetFunctionName(xref.frm)
                function_addr = LocByName(function_name)

                # update cursor
                cur_ea = function_addr
                idc.SetColor(xref.frm, idc.CIC_ITEM, COLOR_ASSEM)

                # print "[!] Entering %s [0x%x] at [0x%x]" % (function_name,
                # function_addr, xref.frm)

                pb = BlockPathFinder(xref.frm)
                pb_results = pb.paths_from(function_addr)
                # print pb_results
                # block_list = map(hex, pb_results)

                '''
                inserted code for making good branch dict
                '''
                GOOD_BRANCH[hex(xref.frm).rstrip(
                    "L")] = hex(cur_ea).rstrip("L")
                # print GOOD_BRANCH

                for pb_result in pb_results:
                    for pb_res in pb_result:
                        # print "STT: " + hex((pb.LookupBlock(pb_res)).startEA).rstrip("L")
                        # print "END: " +
                        # hex((pb.LookupBlock(pb_res)).endEA).rstrip("L")
                        idc.SetColor(pb_res, idc.CIC_ITEM, COLOR_BLOCK)
                        block_list.append(hex(pb_res).rstrip("L"))
                        # print "[block] 0x%x" % pb_res

                # print block_list

                # analyze xref until we reach EP or main
                if cur_ea == src_ea:
                    print "[!] Reached to EP or main"
                    cur_end = True
                    break

            if cur_end:
                break

            AddBpt(xref.frm)


'''
PathFinder code
Starts from here
'''


class PathFinder(object):
    '''
    Base class for finding the path between two addresses.
    '''

    # Limit the max recursion depth
    MAX_DEPTH = 500

    def __init__(self, destination):
        '''
        Class constructor.
        @destination - The end node ea.
        Returns None.
        '''
        self.tree = {}
        self.nodes = {}
        self.depth = 0
        self.last_depth = 0
        self.full_paths = []
        self.current_path = []
        self.destination = destination
        self.build_call_tree(self.destination)
        # print "PathFinder::__init__(dest: 0x%x) called" % (self.destination)

    def __enter__(self):
        return self

    def __exit__(self, t, v, traceback):
        return

    def _name2ea(self, nea):
        if isinstance(nea, type('')):
            return idc.LocByName(nea)
        return nea

    def paths_from(self, source, exclude=[], include=[], xrefs=[], noxrefs=[]):
        '''
        Find paths from a source node to a destination node.
        @source  - The source node ea to start the search from.
        @exclude - A list of ea's to exclude from paths.
        @include - A list of ea's to include in paths.
        @xrefs   - A list of ea's that must be referenced from at least one of the path nodes.
        @noxrefs - A list of ea's that must not be referenced from any of the path nodes.
        Returns a list of path lists.
        '''
        paths = []
        good_xrefs = []
        bad_xrefs = []

        source = self._name2ea(source)

        # If all the paths from the destination node have not already
        # been calculated, find them first before doing anything else.
        if not self.full_paths:
            s = time.time()
            self.find_paths(self.destination, source)
            e = time.time()

        for xref in xrefs:
            xref = self._name2ea(xref)

            for x in idautils.XrefsTo(xref):
                f = idaapi.get_func(x.frm)
                if f:
                    good_xrefs.append(f.startEA)

        for xref in noxrefs:
            bad_xrefs.append(self._name2ea(xref))
            xref = self._name2ea(xref)

            for x in idautils.XrefsTo(xref):
                f = idaapi.get_func(x.frm)
                if f:
                    bad_xrefs.append(f.startEA)

        for p in self.full_paths:
            try:
                index = p.index(source)

                if exclude:
                    for ex in excludes:
                        if ex in p:
                            index = -1
                            break

                if include:
                    orig_index = index
                    index = -1

                    for inc in include:
                        if inc in p:
                            index = orig_index
                            break

                if good_xrefs:
                    orig_index = index
                    index = -1

                    for xref in good_xrefs:
                        if xref in p:
                            index = orig_index

                    if index == -1:
                        print "Sorry, couldn't find", good_xrefs, "in", p

                if bad_xrefs:
                    for xref in bad_xrefs:
                        if xref in p:
                            index = -1
                            break

                # Be sure to include the destinatin and source nodes in the
                # final path
                p = [self.destination] + p[:index + 1]
                # The path is in reverse order (destination -> source), so flip
                # it
                p = p[::-1]
                # Ignore any potential duplicate paths
                if p not in paths:
                    paths.append(p)
            except:
                pass

        return paths

    def find_paths(self, ea, source=None, i=0):
        '''
        Performs a depth-first (aka, recursive) search to determine all possible call paths originating from the specified location.
        Called internally by self.paths_from.
        @ea - The start node to find a path from.
        @i  - Used to specify the recursion depth; for internal use only.
        Returns None.
        '''
        # Increment recursion depth counter by 1
        i += 1
        # Get the current call graph depth
        this_depth = self.depth

        # If this is the first level of recursion and the call
        # tree has not been built, then build it.
        if i == 1 and not self.tree:
            self.build_call_tree(ea)

        # Don't recurse past MAX_DEPTH
        if i >= self.MAX_DEPTH:
            return

        # Loop through all the nodes in the call tree, starting at the
        # specified location
        for (reference, children) in self.nodes[ea].iteritems():
            # Does this node have a reference that isn't already listed in our
            # current call path?
            if reference and reference not in self.current_path:
                    # Increase the call depth by 1
                self.depth += 1
                # Add the reference to the current path
                self.current_path.append(reference)
                # Find all paths from this new reference
                self.find_paths(reference, source, i)

        # If we didn't find any additional references to append to the current call path (i.e., this_depth == call depth)
        # then we have reached the limit of this call path.
        if self.depth == this_depth:
            # If the current call depth is not the same as the last recursive call, and if our list of paths
            # does not already contain the current path, then append a copy of
            # the current path to the list of paths
            if self.last_depth != self.depth and self.current_path and self.current_path not in self.full_paths:
                self.full_paths.append(list(self.current_path))
            # Decrement the call path depth by 1 and pop the latest node out of
            # the current call path
            self.depth -= 1
            if self.current_path:
                self.current_path.pop(-1)

        # Track the last call depth
        self.last_depth = self.depth

    def build_call_tree(self, ea):
        '''
        Performs a breadth first (aka, iterative) search to build a call tree to the specified address.
        @ea - The node to generate a tree for.
        Returns None.
        '''
        self.tree[ea] = {}
        self.nodes[ea] = self.tree[ea]
        nodes = [ea]

        while nodes:
            new_nodes = []

            for node in nodes:
                if node and node != idc.BADADDR:
                    node_ptr = self.nodes[node]

                    for reference in self.node_xrefs(node):
                        if reference not in self.nodes:
                            node_ptr[reference] = {}
                            self.nodes[reference] = node_ptr[reference]
                            new_nodes.append(reference)
                        elif not node_ptr.has_key(reference):
                            node_ptr[reference] = self.nodes[reference]

            nodes = new_nodes

    def node_xrefs(self, node):
        '''
        This must be overidden by a subclass to provide a list of xrefs.
        @node - The EA of the node that we need xrefs for.
        Returns a list of xrefs to the specified node.
        '''
        return []

    def colorize(self, node, color):
        '''
        This should be overidden by a subclass to properly colorize the specified node.
        @node  - The Node object to be colorized.
        @color - The HTML color code.

        Returns None.
        '''
        #idc.SetColor(node, idc.CIC_ITEM, color)


class FunctionPathFinder(PathFinder):
    '''
    Subclass to generate paths between functions.
    '''

    def __init__(self, destination):
        func = idaapi.get_func(self._name2ea(destination))
        super(FunctionPathFinder, self).__init__(func.startEA)
        # print "FunctionPathFinder::__init__(dest: 0x%x) called" %
        # (self.destination)

    def node_xrefs(self, node):
        '''
        Return a list of function EA's that reference the given node.
        '''
        xrefs = []

        for x in XrefsTo(node):
            if x.type != idaapi.fl_F:
                f = idaapi.get_func(x.frm)
                if f and f.startEA not in xrefs:
                    xrefs.append(f.startEA)
        return xrefs

    # def colorize(self, node, color):
    #   '''
    #   Colorize the entire function.
    #   '''
    #   if idc.GetColor(node, idc.CIC_FUNC) != color:
    #       idc.SetColor(node, idc.CIC_FUNC, color)


class BlockPathFinder(PathFinder):
    '''
    Subclass to generate paths between code blocks inside a function.
    '''

    def __init__(self, destination):
        func = idaapi.get_func(destination)
        self.blocks = idaapi.FlowChart(f=func)
        self.block_table = {}

        for block in self.blocks:
            self.block_table[block.startEA] = block
            self.block_table[block.endEA] = block

        self.source_ea = func.startEA
        dst_block = self.LookupBlock(destination)

        if dst_block:
            super(BlockPathFinder, self).__init__(dst_block.startEA)

        # print "BlockPathFinder::__init__(dest: 0x%x) called" %
        # (self.destination)

    def LookupBlock(self, ea):
        try:
            return self.block_table[ea]
        except:
            for block in self.blocks:
                if ea >= block.startEA and ea < block.endEA:
                    return block
        return None

    def node_xrefs(self, node):
        '''
        Return a list of blocks that reference the provided block.
        '''
        xrefs = []

        block = self.LookupBlock(node)
        if block:
            for xref in XrefsTo(block.startEA):
                xref_block = self.LookupBlock(xref.frm)
                if xref_block and xref_block.startEA not in xrefs:
                    xrefs.append(xref_block.startEA)
                    self.colorize(xref_block, 0x70E01B)
        return xrefs

    def colorize(self, node, color):
        '''
        Colorize the entire code block.
        '''
        block = self.LookupBlock(node)
        # print "COLOR!!!!!!!!! from 0x%x to 0x%x" % (block.startEA,
        # block.endEA)

        if block and idc.GetColor(block.startEA, idc.CIC_ITEM) != color:
            ea = block.startEA
            while ea < block.endEA:
                idc.SetColor(ea, idc.CIC_ITEM, color)
                ea += idaapi.decode_insn(ea)


class Find(object):

    def __init__(self, start=[], end=[], include=[], exclude=[], xrefs=[], noxrefs=[]):
        self.start = self._obj2list(start)
        self.end = self._obj2list(end)
        self.include = self._obj2list(include)
        self.exclude = self._obj2list(exclude)
        self.xrefs = self._obj2list(xrefs)
        self.noxrefs = self._obj2list(noxrefs)

        if len(self.start) > 0:
            first_ea = self._obj2ea(self.start[0])
            func = idaapi.get_func(self.start[0])
            if func:
                results = []

                if func.startEA == first_ea:
                    pfclass = FunctionPathFinder
                else:
                    pfclass = BlockPathFinder

                for destination in self.end:
                    pf = pfclass(destination)
                    for source in self.start:
                        results += pf.paths_from(source, exclude=self.exclude,
                                                 include=self.include, xrefs=self.xrefs, noxrefs=self.noxrefs)
                    del pf

                if results:
                    pg = PathFinderGraph(results)
                    pg.Show()
                    del pg

    def _obj2list(self, obj):
        '''
        Converts the supplied object to a list, if it is not already a list.
        @obj - The object.

        Returns a list.
        '''
        l = []

        if not isinstance(obj, type([])):
            l.append(self._obj2ea(obj))
        else:
            for o in obj:
                l.append(self._obj2ea(o))
        return l

    def _obj2ea(self, ea):
        if isinstance(ea, type('')):
            return idc.LocByName(ea)
        return ea


'''
Funcap code
Starts from here
'''


class FunCapHook(DBG_Hooks):
    '''
    Main class to implementing DBG_Hooks
    '''

    # CONSTANTS
    # minimum length requirement to be ascii
    STRING_EXPLORATION_MIN_LENGTH = 4
    # length of discovered strings outputted to file and console
    STRING_LENGTH = 164
    # length of the same strings inserted in IDA code
    STRING_LENGTH_IN_COMMENTS = 82
    # length of single-line hexdumps in hexdump mode outputted to file and
    # console
    HEXMODE_LENGTH = 164
    # length of the same hexdumps inserted in IDA code
    HEXMODE_LENGTH_IN_COMMENTS = 82
    # visited functions will be tagged as follows
    FUNC_COLOR = 0xF7CBEA
    #FUNC_COLOR = 0xF7A0A0
    # visited items (except call instructions) will be tagged as follows
    ITEM_COLOR = 0x70E01B
    # calls will be tagged as follows
    CALL_COLOR = 0x99CCCC
    #CALL_COLOR = 0xB1A0F7
    # maximum comment lines inserted after/before call instructions
    CMT_MAX = 5

    def __init__(self, **kwargs):
        '''

        @param outfile: log file where the output dump will be written (default: %USERPROFILE%\funcap.txt)
        @param delete_breakpoints: delete a breakpoint after first pass ? (default: yes)
        @param hexdump: include hexdump instead of ascii in outfile and IDA comments ? (default: no)
        @param comments: add IDA comments ? (default: yes)
        @param resume: resume program after hitting a breakpoint ? (default: yes)
        @param depth: current stack depth capture for non-function hits (default: 0)
        @param colors: mark the passage with colors ? (default: yes)
        @param output_console: print everything to the console ? (default: yes)
        @param overwrite_existing: overwrite existing capture comment in IDA when the same function is called ? (default: no)
        @param recursive: when breaking on a call - are we recursively hooking all call instructions in the new function ? (default: no)
        @param code_discovery: enable discovery of a dynamically created code - for obfuscators and stuff like that (default: no)
        @param code_discovery_nojmp: don't hook jumps in code_discovery mode (default: no)
        @param code_discovery_stop: stop if new code section is discovered (default: no)
        @param no_dll: disable API calls capturing (default: no)
        @param strings_file: file containing strings dump on captured function arguments (default: %USERPROFILE%\funcap_strings.txt)
        @param multiple_dereferences: dereference each pointer resursively ? (default: 3 levels, 0 - off)

        '''
        self.outfile = kwargs.get(
            'outfile', os.path.expanduser('~') + "/funcap.txt")
        self.delete_breakpoints = kwargs.get('delete_breakpoints', True)
        self.hexdump = kwargs.get('hexdump', False)
        self.comments = kwargs.get('comments', True)
        self.resume = kwargs.get('resume', True)
        self.depth = kwargs.get('depth', 0)
        self.colors = kwargs.get('colors', True)
        self.output_console = kwargs.get('output_console', True)
        self.overwrite_existing = kwargs.get('overwrite_existing', False)
        self.recursive = kwargs.get('recursive', False)
        self.code_discovery = kwargs.get(
            'code_discovery', False)  # for obfuscators
        self.code_discovery_nojmp = kwargs.get('code_discovery_nojmp', False)
        self.code_discovery_stop = kwargs.get('code_discovery_stop', False)
        self.no_dll = kwargs.get('no_dll', False)
        self.strings_file = kwargs.get(
            'strings', os.path.expanduser('~') + "/funcap_strings.txt")
        self.multiple_dereferences = kwargs.get('multiple_dereferences', 3)

        self.visited = []  # functions visited already
        # saved stack contexts - to re-dereference arguments when the function
        # exits
        self.saved_contexts = {}
        self.function_calls = {}  # recorded function calls - used for several purposes
        # brekpoints where FunCap will pause the process to let user start the
        # analysis
        self.stop_points = []
        self.hooked = []  # functions that were already hooked
        self.stub_steps = 0
        self.stub_name = None
        self.current_caller = None  # for single step - before-call context
        # needed in case where single step lands on breakpoint (brekpoint fires
        # first - which is bad...)
        self.delayed_caller = None
        DBG_Hooks.__init__(self)

        self.out = None
        self.strings_out = None
        self.current_callstack = None
        self.runtime_imports = DbgImports()

        debug("FunCapHook::__init__() called", 1)
        # try:
        #     self.current_callstack = None
        #     self.runtime_imports = DbgImports()
        # except:
        #     print "[HADESE] Error opening DbgImports()"

    ###
    # This a is public interface
    # Switches are to be set manually - too lazy to implement setters and getters
    # I started to implement GUI as well but it did not work as expected so it won't be implemented...
    ###

    def on(self):
        '''
        Turn the script on
        '''
        if self.outfile:
            self.out = open(self.outfile, 'w')
        if self.strings_file:
            self.strings_out = open(self.strings_file, 'w')
        self.hook()
        print "FunCap is ON"

    def off(self):
        '''
        Turn the script off
        '''
        if self.out != None:
            self.out.close()
        if self.strings_out != None:
            self.strings_out.close()
        self.unhook()

        print "FunCap is OFF"

    def addFuncStart(self):
        '''
        Add breakpoints on all function starts
        '''
        for f in list(Functions()):
            AddBpt(f)

    def addFuncRet(self):
        '''
        Add breakpoints on all return from subroutine instructions
        '''
        for seg_ea in Segments():
            # For each of the defined elements
            for head in Heads(seg_ea, SegEnd(seg_ea)):

                # If it's an instruction
                if isCode(GetFlags(head)):

                    if self.is_ret(head):
                        AddBpt(head)

    def addCallee(self):
        '''
        Add breakpoints on both function starts and return instructions
        '''
        self.addFuncStart()
        self.addFuncRet()

    def hookFunc(self, jump=False, func=""):
        '''
        Add breakpoints on call instructions within a function

        @param jump: if True, jump instructions will also be hooked in addition to calls - used in code discovery mode
        @param func: this should be a function name. If null, the function that UI cursor points to will be processed

        '''

        if func:
            ea = LocByName(func)
        else:
            ea = ScreenEA()
            func = GetFunctionName(ea)

        self.output("hooking function: %s()" % func)

        chunks = Chunks(ea)
        for (start_ea, end_ea) in chunks:
            if jump:
                self.add_call_and_jump_bp(start_ea, end_ea)
            else:
                self.add_call_bp(start_ea, end_ea)
        self.hooked.append(func)

    def hookSeg(self, seg="", jump=False):
        '''
        Add breakpoints on call instructions within a given segment

        @param jump: if True, jump instructions will also be hooked in addition to calls - used in code discovery mode
        @param seg: this should be a segment name. If null, the segment that UI cursor points to will be processed
        '''

        if seg:
            ea = None
            for s in Segments():
                if seg == SegName(s):
                    ea = s
                    break

            if ea == None:
                self.output("WARNING: cannot hook segment %s" % seg)
                return
        else:
            ea = ScreenEA()
            seg = SegName(ea)
        self.output("hooking segment: %s" % seg)
        start_ea = SegStart(ea)
        end_ea = SegEnd(ea)
        if jump:
            self.add_call_and_jump_bp(start_ea, end_ea)
        else:
            self.add_call_bp(start_ea, end_ea)

    def addCJ(self, func=""):
        '''
        Hook all call and jump instructions

        @param func: name of the function to hook

        '''
        self.hookFunc(jump=True, func=func)

    def delAll(self):
        '''
        Delete all breakpoints
        '''

        for bp in range(GetBptQty(), 0, -1):
            DelBpt(GetBptEA(bp))

    def addStop(self, ea):
        '''
        Add a stop point - the script will pause the process when this is reached

        @param ea: address of the new stop point to add
        '''

        self.stop_points.append(ea)
        AddBpt(ea)

    ###
    # END of public interface
    ###

    def add_call_bp(self, start_ea, end_ea):
        '''
        Add breakpoints on every subrountine call instruction within the given scope (start_ea, end_ea)

        @param start_ea:
        @param end_ea:
        '''

        for head in Heads(start_ea, end_ea):

            # If it's an instruction
            if isCode(GetFlags(head)):

                if self.is_call(head):
                    AddBpt(head)

    def add_call_and_jump_bp(self, start_ea, end_ea):
        '''
        Add breakpoints on every subrountine call instruction and jump instruction within the given scope (start_ea, end_ea)

        @param start_ea:
        @param end_ea:

        '''

        for head in Heads(start_ea, end_ea):

            # If it's an instruction
            if isCode(GetFlags(head)):

                if (self.is_call(head) or self.is_jump(head)):
                    AddBpt(head)

    def get_num_args_stack(self, addr):
        '''
        Get the size of arguments frame

        @param addr: address belonging to a function

        '''

        argFrameSize = GetStrucSize(
            GetFrame(addr)) - GetFrameSize(addr) + GetFrameArgsSize(addr)
        return argFrameSize / (self.bits / 8)

    def get_caller(self):

        return self.prev_ins(self.return_address())

    def format_caller(self, ret):

        return format_offset(ret) + " (0x%x)" % ret

    def getRegValueFromCtx(self, name, context):
        '''
        Extract the value of a single register from the saved context

        @param name: name of the register to extract
        @param context: saved execution context
        '''

        for reg in context:
            if reg['name'] == name:
                return reg['value']

    def add_comments(self, ea, lines, every=False):
        '''
        Insert lines (posterior and anterior lines which are referred to as "comments" in this code) into IDA assembly listing

        @param ea: address where to insert the comments
        @param lines: array of strings to be inserted as multiple lines using ExtLinA()
        @param every: if set to True, the maximum number of lines per address (self.CMT_MAX) will not be respected

        '''

        idx = 0
        for line in lines:
            # workaround with Eval() - ExtLinA() doesn't work well in idapython
            line_sanitized = line.replace('"', '\\"')
            ret = idc.Eval('ExtLinA(%d, %d, "%s");' %
                           (ea, idx, line_sanitized))
            if ret:
                self.output("idc.Eval() returned an error: %s" % ret)
            idx += 1
            if every == False and idx > self.CMT_MAX:
                break

    def format_normal(self, regs):
        '''
        Returns two lists of formatted values and derefs of registers, one for console/file dump, and another for IDA comments (tha latter is less complete)
        Used for everything besides calling and returning from function.

        @param regs: dictionary returned by get_context()
        '''

        full_ctx = []
        cmt_ctx = []

        if self.bits == 32:
            format_string = "%3s: 0x%08x"
            format_string_append = " -> 0x%08x"
            getword = DbgDword
        else:
            format_string = "%3s: 0x%016x"
            format_string_append = " -> 0x%016x"
            getword = DbgQword

        memval = None
        next_memval = None
        prev_memval = None
        valchain_full = ""
        valchain_cmt = ""

        for reg in regs:
            valchain_full = format_string % (reg['name'], reg['value'])
            valchain_cmt = format_string % (reg['name'], reg['value'])
            prev_memval = reg['value']
            memval = getword(reg['value'])
            next_memval = getword(memval)

            if (self.multiple_dereferences):
                maxdepth = self.multiple_dereferences
                while (next_memval):  # memval is a proper pointer
                    if (maxdepth == 0):
                        break
                    maxdepth -= 1
                    if (prev_memval == memval):  # points at itself
                        break
                    valchain_full += format_string_append % memval
                    valchain_cmt += format_string_append % memval

                    prev_memval = memval
                    memval = next_memval
                    next_memval = getword(memval)

            # no more dereferencing. is this a function ?
            function_name = GetFuncOffset(prev_memval)
            if (function_name):
                valchain_full += " (%s)" % function_name
                valchain_cmt += " (%s)" % function_name
            else:  # no, dump data
                if (self.hexdump):
                    valchain_full_left = (
                        self.HEXMODE_LENGTH - len(valchain_full) - 1) / 4
                    valchain_cmt_left = (
                        self.HEXMODE_LENGTH_IN_COMMENTS - len(valchain_cmt) - 1) / 4
                    format_string_dump = " (%s)"
                else:
                    valchain_full_left = self.STRING_LENGTH - \
                        len(valchain_full)
                    valchain_cmt_left = self.STRING_LENGTH_IN_COMMENTS - \
                        len(valchain_cmt)
                    format_string_dump = " (\"%s\")"

                if (valchain_full_left < 4):
                    valchain_full_left = 4  # allways dump at least 4 bytes
                if (valchain_cmt_left < 4):
                    valchain_cmt_left = 4  # allways dump at least 4 bytes

                valchain_full += format_string_dump % self.smart_format(
                    self.dereference(prev_memval, 2 * valchain_full_left), valchain_full_left)
                valchain_cmt += format_string_dump % self.smart_format_cmt(
                    self.dereference(prev_memval, 2 * valchain_cmt_left), valchain_cmt_left)

            full_ctx.append(valchain_full)
            cmt_ctx.append(valchain_cmt)

        return (full_ctx, cmt_ctx)

    def format_call(self, regs):
        '''
        Returns two lists of formatted values and derefs of registers, one for console/file dump, and another for IDA comments
        Used when calling a function.

        @param regs: dictionary returned by get_context()
        '''

        full_ctx = []
        cmt_ctx = []

        if self.bits == 32:
            format_string_full = "%3s: 0x%08x"
            format_string_cmt = "   %3s: 0x%08x"
            format_string_append = " -> 0x%08x"
            getword = DbgDword
        else:
            format_string_full = "%3s: 0x%016x"
            format_string_cmt = "   %3s: 0x%016x"
            format_string_append = " -> 0x%016x"
            getword = DbgQword

        memval = None
        next_memval = None
        prev_memval = None
        valchain_full = ""
        valchain_cmt = ""

        for reg in regs:
            valchain_full = format_string_full % (reg['name'], reg['value'])
            valchain_cmt = format_string_cmt % (reg['name'], reg['value'])
            prev_memval = reg['value']
            memval = getword(reg['value'])
            next_memval = getword(memval)

            if (self.multiple_dereferences):
                maxdepth = self.multiple_dereferences
                while (next_memval):  # memval is a proper pointer
                    if (maxdepth == 0):
                        break
                    maxdepth -= 1
                    if (prev_memval == memval):  # points at itself
                        break
                    valchain_full += format_string_append % memval
                    valchain_cmt += format_string_append % memval

                    prev_memval = memval
                    memval = next_memval
                    next_memval = getword(memval)

            # no more dereferencing. is this a function ?
            function_name = GetFuncOffset(prev_memval)
            if (function_name):
                valchain_full += " (%s)" % function_name
                valchain_cmt += " (%s)" % function_name
            else:  # no, dump data
                if (self.hexdump):
                    valchain_full_left = (
                        self.HEXMODE_LENGTH - len(valchain_full) - 1) / 4
                    valchain_cmt_left = (
                        self.HEXMODE_LENGTH_IN_COMMENTS - len(valchain_cmt) - 1) / 4
                    format_string_dump = " (%s)"
                else:
                    valchain_full_left = self.STRING_LENGTH - \
                        len(valchain_full)
                    valchain_cmt_left = self.STRING_LENGTH_IN_COMMENTS - \
                        len(valchain_cmt)
                    format_string_dump = " (\"%s\")"

                if (valchain_full_left < 4):
                    valchain_full_left = 4  # allways dump at least 4 bytes
                if (valchain_cmt_left < 4):
                    valchain_cmt_left = 4  # allways dump at least 4 bytes

                valchain_full += format_string_dump % self.smart_format(
                    self.dereference(prev_memval, 2 * valchain_full_left), valchain_full_left)
                valchain_cmt += format_string_dump % self.smart_format_cmt(
                    self.dereference(prev_memval, 2 * valchain_cmt_left), valchain_cmt_left)

            full_ctx.append(valchain_full)
            if any(regex.match(reg['name']) for regex in self.CMT_CALL_CTX):
                cmt_ctx.append(valchain_cmt)

        return (full_ctx, cmt_ctx)

    def format_return(self, regs, saved_regs):
        '''
        Returns two lists of formatted values and derefs of registers, one for console/file dump, and another for IDA comments
        Used when returning from function.

        @param regs: dictionary returned by get_context()
        @param saved_regs: dictionary in the format returned by get_context()
        '''

        full_ctx = []
        cmt_ctx = []

        if self.bits == 32:
            format_string_append = " -> 0x%08x"
            format_string_full = "%3s: 0x%08x"
            format_string_cmt = "   %3s: 0x%08x"
            format_string_full_s = "s_%3s: 0x%08x"
            format_string_cmt_s = "   s_%3s: 0x%08x"
            getword = DbgDword
        else:
            format_string_full = "%3s: 0x%016x"
            format_string_cmt = "   %3s: 0x%016x"
            format_string_full_s = "s_%3s: 0x%016x"
            format_string_cmt_s = "   s_%3s: 0x%016x"
            format_string_append = " -> 0x%016x"
            getword = DbgQword

        memval = None
        next_memval = None
        prev_memval = None
        valchain_full = ""
        valchain_cmt = ""

        for reg in regs:
            valchain_full = format_string_full % (reg['name'], reg['value'])
            valchain_cmt = format_string_cmt % (reg['name'], reg['value'])
            prev_memval = reg['value']
            memval = getword(reg['value'])
            next_memval = getword(memval)

            if (self.multiple_dereferences):
                maxdepth = self.multiple_dereferences
                while (next_memval):  # memval is a proper pointer
                    if (maxdepth == 0):
                        break
                    maxdepth -= 1
                    if (prev_memval == memval):  # points at itself
                        break
                    valchain_full += format_string_append % memval
                    valchain_cmt += format_string_append % memval

                    prev_memval = memval
                    memval = next_memval
                    next_memval = getword(memval)

            # no more dereferencing. is this a function ?
            function_name = GetFuncOffset(prev_memval)
            if (function_name):
                valchain_full += " (%s)" % function_name
                valchain_cmt += " (%s)" % function_name
            else:  # no, dump data
                if (self.hexdump):
                    valchain_full_left = (
                        self.HEXMODE_LENGTH - len(valchain_full) - 1) / 4
                    valchain_cmt_left = (
                        self.HEXMODE_LENGTH_IN_COMMENTS - len(valchain_cmt) - 1) / 4
                    format_string_dump = " (%s)"
                else:
                    valchain_full_left = self.STRING_LENGTH - \
                        len(valchain_full)
                    valchain_cmt_left = self.STRING_LENGTH_IN_COMMENTS - \
                        len(valchain_cmt)
                    format_string_dump = " (\"%s\")"

                if (valchain_full_left < 4):
                    valchain_full_left = 4  # allways dump at least 4 bytes
                if (valchain_cmt_left < 4):
                    valchain_cmt_left = 4  # allways dump at least 4 bytes

                valchain_full += format_string_dump % self.smart_format(
                    self.dereference(prev_memval, 2 * valchain_full_left), valchain_full_left)
                valchain_cmt += format_string_dump % self.smart_format_cmt(
                    self.dereference(prev_memval, 2 * valchain_cmt_left), valchain_cmt_left)

            full_ctx.append(valchain_full)
            if any(regex.match(reg['name']) for regex in self.CMT_RET_CTX):
                cmt_ctx.append(valchain_cmt)

        if saved_regs:
            for reg in saved_regs:
                if any(regex.match(reg['name']) for regex in self.CMT_RET_SAVED_CTX):
                    valchain_full = format_string_full_s % (
                        reg['name'], reg['value'])
                    valchain_cmt = format_string_cmt_s % (
                        reg['name'], reg['value'])
                    prev_memval = reg['value']
                    memval = getword(reg['value'])
                    next_memval = getword(memval)

                    if (self.multiple_dereferences):
                        maxdepth = self.multiple_dereferences
                        while (next_memval):  # memval is a proper pointer
                            if (maxdepth == 0):
                                break
                            if (prev_memval == memval):  # points at itself
                                break
                            maxdepth -= 1
                            valchain_full += format_string_append % memval
                            valchain_cmt += format_string_append % memval

                            prev_memval = memval
                            memval = next_memval
                            next_memval = getword(memval)

                    # no more dereferencing. is this a function ?
                    function_name = GetFuncOffset(prev_memval)
                    if (function_name):
                        valchain_full += " (%s)" % function_name
                        valchain_cmt += " (%s)" % function_name
                    else:  # no, dump data
                        if (self.hexdump):
                            valchain_full_left = (
                                self.HEXMODE_LENGTH - len(valchain_full) - 1) / 4
                            valchain_cmt_left = (
                                self.HEXMODE_LENGTH_IN_COMMENTS - len(valchain_cmt) - 1) / 4
                            format_string_dump = " (%s)"
                        else:
                            valchain_full_left = self.STRING_LENGTH - \
                                len(valchain_full)
                            valchain_cmt_left = self.STRING_LENGTH_IN_COMMENTS - \
                                len(valchain_cmt)
                            format_string_dump = " (\"%s\")"

                        if (valchain_full_left < 4):
                            valchain_full_left = 4  # allways dump at least 4 bytes
                        if (valchain_cmt_left < 4):
                            valchain_cmt_left = 4  # allways dump at least 4 bytes

                        valchain_full += format_string_dump % self.smart_format(
                            self.dereference(prev_memval, 2 * valchain_full_left), valchain_full_left)
                        valchain_cmt += format_string_dump % self.smart_format_cmt(
                            self.dereference(prev_memval, 2 * valchain_cmt_left), valchain_cmt_left)

                    full_ctx.append(valchain_full)
                    cmt_ctx.append(valchain_cmt)

        return (full_ctx, cmt_ctx)

    def output(self, line):
        '''
        Standard "print" function used across the whole script

        @param line: line to print
        '''

        if self.outfile:
            self.out.write(line + "\n")
        if self.output_console:
            print line
        if self.outfile:
            self.out.flush()

    def output_lines(self, lines):
        '''
        This prints a list, line by line

        @param lines: lines to print
        '''

        for line in lines:
            if self.outfile:
                self.out.write(line + "\n")
            if self.output_console:
                print line
        if self.outfile:
            self.out.flush()

    # the following few functions are adopted from PaiMei by Pedram Amini
    # they are here to format and present data in a nice way

    def get_ascii_string(self, data):
        '''
        Retrieve the ASCII string, if any, from data. Ensure that the string is valid by checking against the minimum
        length requirement defined in self.STRING_EXPLORATION_MIN_LENGTH.

        @type  data: Raw
        @param data: Data to explore for printable ascii string

        @rtype:  String
        @return: False on failure, ascii string on discovered string.
        '''

        discovered = ""

        for char in data:
            # if we've hit a non printable char, break
            if ord(char) < 32 or ord(char) > 126:
                break

            discovered += char

        if len(discovered) < self.STRING_EXPLORATION_MIN_LENGTH:
            return False

        return discovered

    def get_printable_string(self, data, print_dots=True):
        '''
        description

        @type  data:       Raw
        @param data:       Data to explore for printable ascii string
        @type  print_dots: Bool
        @param print_dots: (Optional, def:True) Controls suppression of dot in place of non-printable

        @rtype:  String
        @return: False on failure, discovered printable chars in string otherwise.
        '''

        discovered = ""

        for char in data:
            if ord(char) >= 32 and ord(char) <= 126:
                discovered += char
            elif print_dots:
                discovered += "."

        return discovered

    def get_unicode_string(self, data):
        '''
        description

        @type  data: Raw
        @param data: Data to explore for printable unicode string

        @rtype:  String
        @return: False on failure, ascii-converted unicode string on discovered string.
        '''

        discovered = ""
        every_other = True

        for char in data:
            if every_other:
                # if we've hit a non printable char, break
                if ord(char) < 32 or ord(char) > 126:
                    break

                discovered += char

            every_other = not every_other

        if len(discovered) < self.STRING_EXPLORATION_MIN_LENGTH:
            return False

        return discovered

    def hex_dump(self, data):
        '''
        Utility function that converts data into one-line hex dump format.

        @type  data:   Raw Bytes
        @param data:   Raw bytes to view in hex dump

        @rtype:  String
        @return: Hex dump of data.
        '''

        dump = ""

        for byte in data:
            dump += "%02x " % ord(byte)

        for byte in data:
            if ord(byte) >= 32 and ord(byte) <= 126:
                dump += byte
            else:
                dump += "."

        return dump

    def dereference(self, address, size):
        return GetManyBytes(address, size, use_dbg=True)

    def smart_format(self, raw_data, maxlen, print_dots=True):
        '''
        "Intelligently" discover data behind an address. The address is dereferenced and explored in search of an ASCII
        or Unicode string. In the absense of a string the printable characters are returned with non-printables
        represented as dots (.). The location of the discovered data is returned as well as either "heap", "stack" or
        the name of the module it lies in (global data).

        @param raw_data:    Binary data to format
        @type  print_dots: Bool
        @param print_dots: (Optional, def:True) Controls suppression of dot in place of non-printable

        @rtype:  String
        @return: String of data discovered behind dereference.
        '''

        if not raw_data:
            return 'N/A'

        try_unicode = raw_data[:maxlen * 2]
        try_ascii = raw_data[:maxlen]

        data = raw_data[:maxlen]
        to_strings_file = None

        data_string = self.get_ascii_string(try_ascii)
        to_strings_file = data_string

        if not data_string:
            data_string = self.get_unicode_string(try_unicode)
            to_strings_file = data_string

        if not data_string and self.hexdump:
            data_string = self.hex_dump(data)

        if not data_string:
            data_string = self.get_printable_string(data, print_dots)

        # shouldn't have been here but the idea of string dumping came out to me later on
        # TODO: re-implement. We could also take much longer strings
        if self.strings_file:
            # that seems not to work very well
            #self.strings_out.write(self.get_printable_string(raw_data, False) + "\n")
            if not to_strings_file:
                to_strings_file = self.get_printable_string(raw_data, False)
            self.strings_out.write(to_strings_file + "\n")
            self.strings_out.flush()

        return data_string

    def smart_format_cmt(self, raw_data, maxlen,  print_dots=True):
        '''
        Same as smart_format() but for IDA comments
        '''

        if not raw_data:
            return 'N/A'

        try_unicode = raw_data[:maxlen * 2]
        try_ascii = raw_data[:maxlen]

        data = raw_data[:maxlen]

        data_string = self.get_ascii_string(try_ascii)

        if not data_string:
            data_string = self.get_unicode_string(try_unicode)

        if not data_string and self.hexdump:
            data_string = self.hex_dump(data)

        if not data_string:
            data_string = self.get_printable_string(data, print_dots)

        return repr(data_string).strip("'")

    def next_ins(self, ea):
        '''
        Return next instruction to ea
        '''
        end = idaapi.cvar.inf.maxEA
        return idaapi.next_head(ea, end)

    def prev_ins(self, ea):
        '''
        Return previous instruction to ea
        '''
        start = idaapi.cvar.inf.minEA
        return idaapi.prev_head(ea, start)

    # handlers called from within debug hooks

    def handle_function_end(self, ea):
        '''
        Called when breakpoint hit on ret instruction
        '''

        function_name = GetFunctionName(ea)
        caller = self.format_caller(self.get_caller())
        if function_name:
            header = "At function end: %s (0x%x) " % (
                function_name, ea) + "to " + caller
            raw_context = self.get_context(ea=ea)
        else:
            header = "At function end - unknown function (0x%x) " % ea + \
                "to " + caller
            raw_context = self.get_context(ea=ea, depth=0)
        if self.colors:
            SetColor(ea, CIC_ITEM, self.ITEM_COLOR)
        (context_full, context_comments) = self.format_normal(raw_context)
        if self.delete_breakpoints:
            DelBpt(ea)

        if self.comments and (self.overwrite_existing or ea not in self.visited):
            self.add_comments(ea, context_comments, every=True)

        self.visited.append(ea)
        self.output_lines([header] + context_full + [""])

    def handle_return(self, ea):
        '''
        Called when breakpoint hit on next-to-call instruction
        '''

        # need to get context from within a called function
        function_call = self.function_calls[ea]
        ret_shift = function_call['ret_shift']
        raw_context = self.get_context()
        # raw_context = self.get_context(stack_offset = 0 - ret_shift,
        # depth=function_call['num_args'] - ret_shift) # no stack here ?

        sp = self.get_sp()
        sp = sp - ret_shift
        if self.saved_contexts.has_key(sp):
            saved_context = self.saved_contexts[sp]['ctx']
            func_name = self.saved_contexts[sp]['func_name']
            del self.saved_contexts[sp]
        else:
            func_name = function_call['func_name']
            self.output("WARNING: saved context not found for stack pointer 0x%x, assuming function %s" % (
                sp, function_call['func_name']))
            saved_context = None

        header = "Returning from call to %s(), execution resumed at %s (0x%x)" % (
            func_name, format_offset(ea), ea)
        (context_full, context_comments) = self.format_return(
            raw_context, saved_context)

        if self.comments and (self.overwrite_existing or ea not in self.visited):
            self.add_comments(ea, context_comments)
        self.visited.append(ea)
        self.output_lines([header] + context_full + [""])

    def handle_function_start(self, ea):
        '''
        Called when breakpoint hit on the beginning of a function
        '''

        name = GetFunctionName(ea)

        caller_ea = self.get_caller()
        caller_offset = self.format_caller(caller_ea)
        caller_name = format_name(caller_ea)

        header = "At function start: %s (0x%x) " % (
            name, ea) + "called by %s" % caller_offset

        raw_context = self.get_context(ea=ea)
        if self.colors:
            SetColor(ea, CIC_FUNC, self.FUNC_COLOR)

        (context_full, context_comments) = self.format_normal(raw_context)

        if self.comments and (self.overwrite_existing or ea not in self.visited):
            self.add_comments(ea, context_comments, every=True)

        self.visited.append(ea)

        self.visited.append(ea)
        self.output_lines([header] + context_full + [""])

    def handle_generic(self, ea):
        '''
        Called when breakpoint hit on anything else besides the above and below
        '''

        header = "Address: 0x%x" % ea
        # no argument dumping if not function
        raw_context = self.get_context(ea=ea, depth=self.depth)
        (context_full, context_comments) = self.format_normal(raw_context)
        if self.colors:
            SetColor(ea, CIC_ITEM, self.ITEM_COLOR)

        if self.comments and (self.overwrite_existing or ea not in self.visited):
            self.add_comments(ea, context_comments)

        self.visited.append(ea)
        self.output_lines([header] + context_full + [""])

    def handle_call(self, ea):
        '''
        Called when breakpoint hit on a call instruction.
        '''

        # print "in handle_call()"

        if self.current_caller:  # delayed_caller: needed if breakpoint hits after signle step request
            self.delayed_caller = {
                'type': 'call', 'addr': ea, 'ctx': self.get_context(ea=ea, depth=0)}
        else:
            self.current_caller = {
                'type': 'call', 'addr': ea, 'ctx': self.get_context(ea=ea, depth=0)}

        # print "handle_call: 0x%x" % ea
        if self.colors:
            SetColor(ea, CIC_ITEM, self.CALL_COLOR)

    def handle_jump(self, ea):
        '''
        Called when breakpoint hits on a jump instruction when code_discovery mode enabled
        '''

        if self.current_caller:
            self.delayed_caller = {'type': 'jump', 'addr': ea}
        else:
            self.current_caller = {'type': 'jump',
                                   'addr': ea}  # don't need ctx here

    def handle_after_jump(self, ea):
        '''
        Called when single stepping into a jmp instruction
        '''

        if self.comments:
            MakeComm(self.current_caller['addr'], "0x%x" % ea)
        seg_name = SegName(ea)
        if self.code_discovery and (not isCode(GetFlags(ea)) or not self.isCode) and not self.is_system_lib(seg_name):
            self.output("New code segment discovered: %s (0x%x => 0x%x)" %
                        (seg_name, self.current_caller['addr'], ea))
            start_ea = SegStart(ea)
            end_ea = SegEnd(ea)
            refresh_debugger_memory()
            if not MakeCode(ea):
                ins = DecodeInstruction(ea)
                if ins.size:
                    MakeUnknown(ea, ins.size, DOUNK_EXPAND)
                    if not MakeCode(ea):
                        self.output(
                            "handle_after_jump(): unable to make code at 0x%x" % ea)

            AnalyzeArea(start_ea, end_ea)
            self.add_call_and_jump_bp(start_ea, end_ea)

        self.current_caller = self.delayed_caller
        self.delayed_caller = None

    def discover_function(self, ea):
        '''
        Try to get a name of a function. If function does not exists at ea, tries to create/discover it.
        '''

        name = GetFunctionName(ea)
        symbol_name = Name(ea)

        if symbol_name and name and symbol_name != name and not re.match("loc_", symbol_name):
            self.output("WARNING: IDA has probably wrongly analyzed the following function: %s and "
                        "it is overlapping with another symbol: %s. Funcap will undefine it. " % (name, symbol_name))
            DelFunction(LocByName(name))
            name = None

        if name:
            return name

        need_hooking = False
        # refresh_debugger_memory() # SegName didn't seem to work sometimes
        seg_name = SegName(ea)
        if self.code_discovery and not self.is_system_lib(seg_name) and (not isCode(GetFlags(ea)) or not self.isCode):
            # print "need_hooking :: ea: %x, seg_name: %s" % (ea, seg_name)
            need_hooking = True

        refresh_debugger_memory()  # need to call this here (thx IlfakG)
        # this should normally work for dynamic libraries

        r = MakeFunction(ea)
        if not r:
            # this might be dynamically created code (such as obfuscation etc.)
            if MakeCode(ea):
                # fine, we try again
                r = MakeFunction(ea)
                if not r:
                    self.output(
                        "WARNING: unable to create function at 0x%x" % ea)
            else:
                # undefining also helps. Last try (thx IgorS)
                ins = DecodeInstruction(ea)
                if ins.size:
                    MakeUnknown(ea, ins.size, DOUNK_EXPAND)
                    if MakeCode(ea):
                        # weird but worked on my example ... calling the same
                        # twice
                        refresh_debugger_memory()
                        r = MakeFunction(ea)
                        refresh_debugger_memory()
                        r = MakeFunction(ea)
                        if not r:
                            self.output(
                                "WARNING: unable to create function at 0x%x" % ea)

        if need_hooking:
            start_ea = SegStart(ea)
            end_ea = SegEnd(ea)
            refresh_debugger_memory()
            self.output("0x%x: new code section detected: [0x%x, 0x%x]" % (
                ea, start_ea, end_ea))
            AnalyzeArea(start_ea, end_ea)
            if self.code_discovery_stop:
                self.resume = False
            if self.code_discovery_nojmp:
                self.add_call_bp(start_ea, end_ea)
            else:
                self.add_call_and_jump_bp(start_ea, end_ea)

        if r:
            name = GetFunctionName(ea)
            func_end = GetFunctionAttr(ea, FUNCATTR_END)
            AnalyzeArea(ea, func_end)
            return name
        else:
            return None

    def handle_after_call(self, ret_addr, stub_name):
        '''
        Called when single stepping into a call instruction (lands at the beginning of a function)
        '''

        ea = self.get_ip()

        if self.is_fake_call(ea):
            MakeComm(self.current_caller['addr'],
                     "fake function call to 0x%x" % ea)
            self.output("0x%X: fake function call to 0x%x" %
                        (self.current_caller['addr'], ea))
            self.current_caller = self.delayed_caller
            self.delayed_caller = None
            return 0

        # print "handle_after_call(): 0x%x" % ea

        seg_name = SegName(ea)

        if self.no_dll and self.is_system_lib(seg_name):
            # skipping API calls
            self.current_caller = self.delayed_caller
            self.delayed_caller = None
            return 0

        caller_ea = self.current_caller['addr']
        caller = format_offset(caller_ea)
        caller_name = format_name(caller_ea)

        arguments = []
        num_args = 0

        name = self.discover_function(ea)

        # if it's a real function (should be), capture stack-based arguments

        if name:
            num_args = self.get_num_args_stack(ea)
            arguments = self.get_stack_args(ea=ea, depth=num_args + 1)
            # if recursive or code_discover mode, hook the new functions with
            # breakpoints on all calls (or jumps)
            if (self.recursive or self.code_discovery) and not self.is_system_lib(seg_name) and name not in self.hooked:
                self.hookFunc(func=name)
        else:
            # maybe there is a symbol (happens sometimes when the IDA analysis
            # goes wrong)
            name = Name(ea)
            if not name:
                name = "0x%x" % ea
            # this probably is not a real function then - handle it in a
            # generic way
            self.output("Call to unknown function: 0x%x to %s" %
                        (caller_ea, name))
            self.handle_generic(ea)
            self.current_caller = self.delayed_caller
            self.delayed_caller = None
            return 0

        # if we were going through a stub, display the name that was called
        # directly (e.g. not kernelbase but kernel32)
        if self.stub_name:
            header = "Function call: %s to %s (0x%x)" % (caller, stub_name, ea) +\
                "\nReal function called: %s" % name
        else:
            header = "Function call: %s to %s (0x%x)" % (caller, name, ea)

        # link previously captured register context with stack-based arguments

        raw_context = self.current_caller['ctx'] + arguments
        self.current_caller = self.delayed_caller
        self.delayed_caller = None

        if CheckBpt(ret_addr) > 0:
            user_bp = True
        else:
            user_bp = False
            # catch return from the function if not user-added breakpoint
            AddBpt(ret_addr)

        # fetch the operand for "ret" - will be needed when we will capture the
        # return from the function
        ret_shift = self.calc_ret_shift(ea)

        # this is to be able to reference to this call instance when we are returning from this function
        # try to do it via the satck
        call_info = {'ctx': raw_context, 'calling_addr': caller_ea, 'func_name': name,
                     'func_addr': ea, 'num_args': num_args, 'ret_shift': ret_shift, 'user_bp': user_bp}

        self.saved_contexts[self.get_saved_sp(raw_context)] = call_info

        # if no stack pointer matches while returning (which sometimes happends, unfortunately), try to match it via a fallback method
        # this gives a right guess most of the time, unless some circumstances
        # arise with multiple threads
        self.function_calls[ret_addr] = call_info

        # output to the console and/or file
        (context_full, context_comments) = self.format_call(raw_context)
        self.output_lines([header] + context_full + [""])

        # we prefer kernel32 than kernelbase etc. - this is to bypass stubs
        # if self.stub_name:
        #    name = self.stub_name

        # insert IDA's comments
        if self.comments and (self.overwrite_existing or caller_ea not in self.visited):
            self.add_comments(caller_ea, context_comments)
            MakeComm(caller_ea, "%s()" % name)

        # next time we don't need to insert comments (unles overwrite_existing
        # is set)
        self.visited.append(caller_ea)

        if self.colors:
            SetColor(ea, CIC_FUNC, self.FUNC_COLOR)

    def is_system_lib(self, name):
        '''
        Returns true if a segment belongs to a system library, in which case we don't want to recursively hook calls.
        Covers Windows, Linux, Mac, Android, iOS

        @param name: segment name
        '''

        # the below is for Windows kernel debugging
        if name == 'nt':
            return True

        sysfolders = [re.compile("\\\\windows\\\\", re.I), re.compile("\\\\Program Files ", re.I), re.compile("/usr/", re.I),
                      re.compile("/system/", re.I), re.compile("/lib/", re.I)]
        m = GetFirstModule()
        while m:
            path = GetModuleName(m)
            if re.search(name, path):
                if any(regex.search(path) for regex in sysfolders):
                    return True
                else:
                    return False
            m = GetNextModule(m)
        return False

    ###
    # debugging hooks
    ###

    def dbg_bpt(self, tid, ea):
        '''
        Callback routine called each time the breakpoint is hit
        '''

        # print "dbg_bpt(): 0x%x" % ea

        refresh_debugger_memory()
        is_func_start = False

        if ea in self.stop_points:
            print "FunCap: reached a stop point"
            return 0

        if ea in self.function_calls.keys():  # coming back from a call we previously stopped on
            self.handle_return(ea)
            if self.function_calls[ea]['user_bp'] == False:
                DelBpt(ea)
                if self.resume:
                    request_continue_process()
                    run_requests()
                return 0

        if ea in Functions():  # start of a function
            self.handle_function_start(ea)
            is_func_start = True

        if self.is_ret(ea):  # stopped on a ret instruction
            self.handle_function_end(ea)

        elif self.is_jump(ea) and self.code_discovery:
            self.handle_jump(ea)
            request_step_into()
            run_requests()
            # we don't want ResumeProcess() to be called so we end it up here
            if self.delete_breakpoints:
                DelBpt(ea)
            return 0

        elif self.is_call(ea):  # stopped on a call to a function
            # we need to register context before step in
            self.handle_call(ea)
            # requesting step_into on call instruction: don't know if this is
            # the proper way but it works like that
            request_step_into()
            run_requests()
            if self.delete_breakpoints:
                DelBpt(ea)
            return 0

        else:  # not call, not ret, and not start of any function
            if not is_func_start:
                self.handle_generic(ea)

        if self.delete_breakpoints:
            DelBpt(ea)
        if self.resume:
            request_continue_process()
            run_requests()

        return 0

    def dbg_step_into(self):
        '''
        Standard callback routine for stepping into.
        '''
        # if we are currently bouncing off a stub, bounce one step further

        ea = self.get_ip()
        # ea = get_cur_ea()

        try:
            debug("library_name retrieving", 2)
            debug("library_name retreiving", 2)
            (iatEA, library_name) = self.runtime_imports.find_func_iat_adrs(ea)
            debug("library_name: " + library_name, 2)
        except:
            debug("library_name retrieve error", 2)

        try:
            debug("function_name retreiving", 2)
            func_call_num = self.current_callstack.push(
                ea, iatEA, library_name=library_name, calling_ea=self.prev_bp_ea)
            (func_adr, func_name) = self.current_callstack.get_top_func_data()
            debug("function_name: " + func_name, 2)
        except:
            debug("library_name retrieve error", 1)

        refresh_debugger_memory()
        # print "dbg_step_into(): 0x%x" % ea

        if self.stub_steps > 0:
            self.stub_steps = self.stub_steps - 1
            request_step_into()
            run_requests()
            return 0

        # check if need to bounce a new stub
        self.stub_steps = self.check_stub(ea)
        # print "check_stub(): %x : %d" % (ea, self.stub_steps)
        if self.stub_steps > 0:
            self.stub_name = Name(ea)
            # print "in self.stub_steps > 0: Name: %s" % self.stub_name
            self.stub_steps = self.stub_steps - 1
            request_step_into()
            run_requests()
            return 0

        if hasattr(self, 'current_caller') and self.current_caller and self.current_caller['type'] == 'jump':
            self.handle_after_jump(ea)
        else:
            # type must be call
            ret_addr = self.return_address()

            if hasattr(self, 'current_caller') and self.current_caller and ret_addr == self.next_ins(self.current_caller['addr']):
                self.handle_after_call(ret_addr, self.stub_name)
                self.stub_name = None
            else:
                # that's not us - return to IDA
                self.current_caller = None
                self.delayed_caller = None
                if self.resume:
                    # happens sometimes - due to a BUG in IDA. Hope one day it
                    # will be corrected
                    "FunCap: unexpected single step"
        if self.resume:
            request_continue_process()
            run_requests()

        return 0


'''
X86CapHook code
Starts from here
'''


class X86CapHook(FunCapHook):
    '''
    X86 32-bit architecture
    '''

    def __init__(self, **kwargs):
        self.arch = 'x86'
        self.bits = 32
        self.CMT_CALL_CTX = [re.compile('^arg')]
        self.CMT_RET_CTX = [re.compile('^EAX')]
        self.CMT_RET_SAVED_CTX = [re.compile('^arg')]
        self.CMT_MAX = 4
        FunCapHook.__init__(self, **kwargs)

    def is_ret(self, ea):
        '''
        Check if we are at return from subroutine instruction
        '''
        mnem = GetMnem(ea)
        return re.match('ret', mnem)

    def is_call(self, ea):
        '''
        Check if we are at jump to subrouting instruction
        '''
        mnem = GetDisasm(ea)
        if re.match('call\s+far ptr', mnem):
            return None  # when IDA badly identifies data as code it throws false positives - zbot example
        return re.match('call', mnem)

    def is_jump(self, ea):
        '''
        Check if we are at jump to subrouting instruction
        '''
        mnem = GetMnem(ea)
        return re.match('jmp', mnem)

    def get_context(self, general_only=True, ea=None, depth=None, stack_offset=1):
        '''
        Captures register states + arguments on the stack and returns it in an array
        We ask IDA for number of arguments to look on the stack

        @param general_only: only general registers (names start from E)
        @param ea: Address belonging to a function. If not None, stack will be examined for arguments
        @param depth: stack depth to capture - if None then number of it is determined automatically based on number of arguments in the function frame
        '''
        regs = []
        for x in idaapi.dbg_get_registers():
            name = x[0]
            if not general_only or (re.match("E", name) and name != 'ES'):
                value = idc.GetRegValue(name)
                regs.append({'name': name, 'value': value, 'deref': self.dereference(
                    value, 2 * self.STRING_LENGTH)})
        if ea != None or depth != None:
            regs = regs + \
                self.get_stack_args(ea, depth=depth, stack_offset=stack_offset)
        return regs

    def get_stack_args(self, ea, depth=None, stack_offset=1):
        '''
        Captures args from memory. If not depth given, number of args is dynamically created from IDA's analysis
        '''
        l = []
        stack = idc.GetRegValue('ESP')
        if depth == None:
            depth = self.get_num_args_stack(ea) + 1
        argno = 0
        for arg in range(stack_offset, depth):
            value = DbgDword(stack + arg * 4)
            l.append({'name': "arg_%02x" % argno, 'value': value,
                      'deref': self.dereference(value, 2 * self.STRING_LENGTH)})
            argno = argno + 4
        return l

    def get_ip(self):
        return GetRegValue('EIP')

    def get_sp(self):
        return GetRegValue('ESP')

    def get_saved_sp(self, context):
        return self.getRegValueFromCtx('ESP', context)

    def return_address(self):
        '''
        Get the return address stored on the stack or register
        '''
        return DbgDword(GetRegValue('ESP'))

    def calc_ret_shift(self, ea):
        '''
        Calculates additional stack shift when returning from a function e.g. for 'ret 5h' it will return 5

        @param ea: address belonging to a function
        '''

        first_head = GetFunctionAttr(ea, FUNCATTR_START)
        curr_head = PrevHead(GetFunctionAttr(ea, FUNCATTR_END))
        while curr_head >= first_head:
            mnem = GetMnem(curr_head)
            ret_match = re.match('ret', mnem)
            if ret_match:
                break
            curr_head = PrevHead(curr_head)
        if curr_head >= first_head:
            op = GetOpnd(curr_head, 0)
            if op:
                ret_shift = int(re.sub('h$', '', op), 16)
            else:
                ret_shift = 0
        if not ret_match:
            self.output(
                "WARNING: no ret instruction found in the function body, assuming 0x0 shift")
            ret_shift = 0

        return ret_shift

    def check_stub(self, ea):
        '''
        Checks if we are calling into a stub instead of a real function. Currently only supports MS compiler / Windows 7 API (like kernel32.dll)
        There are more to implement, for example Cygwin uses different ones that are not currently supported.

        @param ea: address to check for a stub
        '''

        # several different types of stubs spotted in kernel32.dll one Windows 7 32bit, maybe others dll as well ?
        # type 1 - simple jump to offset - need to do 1 single step

        # a bit of a workaround - we need to know if it is code or note before
        # making it code. Needed for code_discovery

        if(isCode(GetFlags(ea))):
            self.isCode = True
        else:
            self.isCode = False
            MakeCode(ea)

        disasm = GetDisasm(ea)
        if re.match('^jmp', disasm):
            # print "in check_stub(): JMP stub detected"
            return 1
        # type 2 - strange do-nothing-instruction chain like the below
        # kernel32.dll:76401484 8B FF                         mov     edi, edi
        # kernel32.dll:76401486 55                            push    ebp
        # kernel32.dll:76401487 8B EC                         mov     ebp, esp
        # kernel32.dll:76401489 5D                            pop     ebp
        # kernel32.dll:7640148A E9 2D FF FF FF                jmp
        # sub_764013BC
        dbytes = GetManyBytes(ea, 7, use_dbg=True)
        if dbytes == "\x8b\xff\x55\x8b\xec\x5d\xe9" or dbytes == "\x8b\xff\x55\x8b\xec\x5d\xeb":
            return 5
        # no stubs. You can define your custom stubs here
        return 0

    def is_fake_call(self, ea):
        '''
        Check if it is a fake call and function should not be analyzed there
        Currently only checking call-to-pops, what else ?
        '''
        mnem = GetMnem(ea)
        return re.match('pop', mnem)


###
# main()
###
if __name__ == '__main__':

    # script on/off initializing
    # d.off()
    d = X86CapHook()
    # a = Auto()
    d.on()

    # explore target APIs
    explore_api()

    # cur = ScreenEA()
    cur = GetEntryOrdinal(0)

    # explore paths
    for ea in USER_DEFINED_ADDR:
        explore_path(cur, ea)


'''
path-finder
path to connect API
'''

# debug("run_request", 1)
# start_process()
