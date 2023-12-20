import sys
import os
import json
import argparse
import re
from antlr4 import *
from tools.YulListener import YulListener
from tools.YulParser import YulParser

from bigtree import Node, BaseNode
import textwrap

class PrintableNode(Node):
    def to_str(self):
        return ("\n").join([c.to_str() for c in self.children])

    def prepare(self):
        c = [c.prepare() for c in self.children]

    def find_parent_proc(self,cur):
        if isinstance (cur.parent, ProcNode):
            return cur.parent
        elif cur.parent != None:
            return self.find_parent_proc(cur.parent)
        else:
            return None




    def indent(self, text, amount, ch=' '):
        return textwrap.indent(text, amount * ch)

class EmptyNode(PrintableNode):
    pass

class RootNode(PrintableNode):
    def __init__(self, name, sep = '/', **kwargs):
        super().__init__(name,sep, **kwargs)
        self.proc_list = ["mload","mstore","mstore8","keccak256","add","lt", "addmod","sub","iszero","mul", "div","mod","or","eq","gas","and","shr","shl","gt","verbatim_2i_1o"]
        self.str_constants = []
        
    def to_str(self):
        import_module = "require import AllCore.\nrequire import YulEasyCryptModel.\n\n"
        constants = "\n".join(["op " + c + " : uint256." for c in self.str_constants])
        module_body = ("\n").join([c.to_str() for c in self.children])
        module_body = self.indent(module_body,4,' ')        
        return import_module + "\n" + constants + "\n" + "module YulExtract = {\n    var m : memory\n \n" + self.pre_setup() + module_body + "\n}."

    def pre_setup(self):
        funcs = """
    proc mload(a: uint256) = {
      return mload(m,a);
    }
    proc mstore(a: uint256, v : uint256) : unit = {
      m <- mstore(m,a,v); 
      return ();
    }        
    proc mstore8(a: uint256, v : uint256) : unit = {
      m <- mstore(m,a,v);
      return ();
    }        
    proc keccak256(s: uint256, o : uint256) : uint256 = {
      return keccak256(m,s,o);  
    }
    proc add(v1: uint256, v2 : uint256) : uint256 = {
      return add(v1,v2);  
    }
    proc sub(v1: uint256, v2 : uint256) : uint256 = {
      return sub(v1,v2);  
    }
    proc mul(v1: uint256, v2 : uint256) : uint256 = {
      return mul(v1,v2);  
    }
    proc mod(v1: uint256, v2 : uint256) : uint256 = {
      return mod(v1,v2);  
    }
    proc or(v1: uint256, v2 : uint256) : uint256 = {
      return or(v1,v2);  
    }        
    proc div(v1: uint256, v2 : uint256) : uint256 = {
      return div(v1,v2);  
    }        
    proc lt(v1: uint256, v2 : uint256) : uint256 = {
      return lt(v1,v2);  
    }
    proc gt(v1: uint256, v2 : uint256) : uint256 = {
      return gt(v1,v2);  
    }        
    proc iszero(v: uint256) : uint256 = {
      return iszero(v);  
    }        
    proc addmod(v1: uint256, v2 : uint256, mod: uint256) : uint256 = {
      return addmod(v1,v2,mod);  
    }
    proc eq(v1: uint256, v2 : uint256) : uint256 = {
      return eq(v1,v2);  
    }
    proc and(v1: uint256, v2 : uint256) : uint256 = {
      return and(v1,v2);  
    }
    proc shl(v1: uint256, v2 : uint256) : uint256 = {
      return shl(v1,v2);  
    }
    proc shr(v1: uint256, v2 : uint256) : uint256 = {
      return shr(v1,v2);  
    }
    proc gas() : uint256 = { 
        return witness;
    }
    proc verbatim_2i_1o(f : uint256, a1 : uint256, a2 : uint256) : uint256 = { 
        return witness;
    }        
"""
        return funcs


class BlockNode(PrintableNode):
    def __init__(self, name, sep = '/', **kwargs):
        super().__init__(name,sep, **kwargs)


class ExpressionNode(PrintableNode):
    def __init__(self, name, sep = '/', **kwargs):
        super().__init__(name,sep, **kwargs)

    def pre(self):
        return ("\n").join([c.pre() for c in self.children])

    def flat(self):
        return ("\n").join([c.flat() for c in self.children])

    def var_repr(self):
        if isinstance(self.children[0], FunctionCallNode):
            return self.children[0].name
        elif isinstance(self.children[0], LiteralNode):
            return  self.children[0].literal_value
        elif isinstance(self.children[0], IdentifierNode):
            return  self.children[0].id_value

class IdentifierNode(PrintableNode):
    def __init__(self, name, sep = '/', **kwargs):
        super().__init__(name,sep, **kwargs)
        self.id_value =  ""
    def to_str(self, flat = False):
        return self.id_value
    def flat(self):
        return self.id_value
    def pre(self):
        return ""


class LiteralNode(PrintableNode):
    def __init__(self, name, sep = '/', **kwargs):
        super().__init__(name,sep, **kwargs)
        self.literal_value =  ""
    def to_str(self, flat = False):
        return self.literal_value
    def flat(self):
        return self.literal_value  
    def pre(self):
        return ""
    def is_proc(self):
        return False
    def setLiteralValue(self, v):
        self.literal_value = v



class FunctionCallNode(PrintableNode):
    def __init__(self, name, sep = '/',  **kwargs):
        super().__init__(name,sep, **kwargs)
        self.func_name = ""
        self.ass_child = False

    def to_str(self):
        s = self.func_name + "(" + (",").join([c.flat() for c in self.children]) + ");" 
        s = ("").join([c.pre() for c in self.children]) + s + "\n"
        return s

    def pre(self):
        s = ("").join([c.pre() for c in self.children])
        if not self.ass_child :
            s +=  self.name + (" <@ " if self.is_proc() else " <- ") + self.func_name + "(" + (",").join([c.flat() for c in self.children]) + ");" + "\n"

            
        return s

    def is_proc(self):
        return (self.func_name in self.root.proc_list)
        

    def flat(self):
        return self.name

    def first_layer(self):
        s =  self.func_name + "(" + (",").join([c.flat() for c in self.children]) + ")" 
        return s

    def prepare(self):
        if isinstance (self.parent.parent, FunctionCallNode) or isinstance (self.parent.parent, AssNode) or isinstance(self.parent.parent, VarDeclNode) or isinstance(self.parent.parent, IfNode) or isinstance(self.parent.parent, SwitchNode) :
            if not self.ass_child:
                proc = self.find_parent_proc(self)
                proc.proc_vars.append(self.name)
        super().prepare()

    def setFunctionCallName(self,name):
        self.func_name = ("_" if name[0].isupper() else "")  + name

        

    


class AssNode(PrintableNode):
    def __init__(self, name, sep = '/', **kwargs):
        super().__init__(name,sep, **kwargs)
        self.lhs = []
        self.rhs = LiteralNode("lit")

    def to_str(self):
        lhs = ", ".join(self.lhs)
        if len(self.lhs) > 1:
            lhs = "(" + lhs + ")"
        if(isinstance(self.rhs, FunctionCallNode)):
            rhs = self.rhs.first_layer()            
            pre = self.rhs.pre()
            ass_mode = "<@" if self.rhs.is_proc() else "<-"
        else:
            rhs = self.rhs.flat()
            pre = self.rhs.pre()
            ass_mode = "<-"

        s = """{lhs} {ass_mode} {rhs};""".format(lhs = lhs , rhs = rhs, ass_mode = ass_mode )
        s = pre + s
        return s


class VarDeclNode(PrintableNode):
    def __init__(self, name, sep = '/', **kwargs):
        super().__init__(name,sep, **kwargs)
        self.lhs = []
        self.rhs = LiteralNode("lit")

    def to_str(self):
        lhs = ", ".join(self.lhs)
        if len(self.lhs) > 1:
            lhs = "(" + lhs + ")"
        if(isinstance(self.rhs, FunctionCallNode)):
            rhs = self.rhs.first_layer()            
            pre = self.rhs.pre()
            ass_mode = "<@" if self.rhs.is_proc() else "<-"
        else:
            rhs = self.rhs.flat()
            pre = self.rhs.pre()
            ass_mode = "<-"

        s = """{lhs} {ass_mode} {rhs};""".format(lhs = lhs , rhs = rhs,ass_mode = ass_mode)
        s = pre + s
        return s

    def prepare(self):
        proc = self.find_parent_proc(self)
        proc.proc_vars += self.lhs
        super().prepare()



class IfNode(PrintableNode):
    def __init__(self, name, sep = '/', **kwargs):
        super().__init__(name,sep, **kwargs)

        

    def to_str(self):
        s = self.children[0].pre()
        if_body = "\n".join([c.to_str() for c in self.children[1:]])
        if_body = self.indent(if_body,4,' ')
        s = s + "if(as_bool " + self.children[0].flat() + "){\n" + if_body  + "\n}"
        return s


class CaseNode(PrintableNode):
    def __init__(self, name, sep = '/', **kwargs):
        super().__init__(name,sep, **kwargs)
        self.cond = None
        self.else_branch = None

    def to_str(self):
        case_lit = self.children[0].to_str()
        case_body = self.indent(self.children[1].to_str(),4,' ')

        s = "if(as_bool (eq(" + self.cond.flat() + "," + case_lit  + "))"  + "){\n" + case_body  + "\n}"
        if self.else_branch != None:
            s += "else{\n" + self.indent(self.else_branch.to_str(),4,' ') + "\n}"
        return s        

class SwitchNode(PrintableNode):
    def __init__(self, name, sep = '/', **kwargs):
        super().__init__(name,sep, **kwargs)

    def to_str(self):
        s = self.children[0].pre()
        prev = None
        for c in self.children[1:]:
            c.cond = self.children[0]

            if prev != None:
                prev.else_branch = c

            prev = c


        s += self.children[1].to_str()
        
        return s


    def prepare(self):
        super().prepare()



class ForNode(PrintableNode):
    def __init__(self, name, sep = '/', **kwargs):
        super().__init__(name,sep, **kwargs)
# TODO: add vars
    def to_str(self):
        cond_var = self.children[1].var_repr()
        init_block = self.children[0].to_str()
        cond_block = self.children[1].pre()
        cond_block_init = self.children[1].pre()
        post_block = self.indent(self.children[2].to_str(),4,' ')
        body_block = self.indent(self.children[3].to_str(),4,' ')
        return init_block + "\n" + cond_block_init + "while(as_bool " + cond_var + "){\n" + body_block + "\n" + post_block + "\n" + self.indent(cond_block,4,' ') + "\n}"

    def prepare(self):
        if isinstance(self.children[1].children[0], FunctionCallNode):
            proc = self.find_parent_proc(self)
            proc.proc_vars.append(self.children[1].var_repr())
        super().prepare()

    


class ProcNode(PrintableNode):
    def __init__(self, name, sep = '/', **kwargs):
        super().__init__(name,sep, **kwargs)
        self.proc_name = None
        self.proc_args = []
        self.proc_return_type = []
        self.proc_vars = []
        
    def prepare(self):
        self.root.proc_list.append(self.proc_name)
        super().prepare()
    
    
    def to_str(self):
        cur_vars = [i[0] for i in self.proc_return_type] + self.proc_vars
        cur_vars = [ ("_" if c[0].isupper() else "") + c for c in cur_vars]

        rett = " * ".join(["uint256" for _ in range(len(self.proc_return_type))])
        proc_body = ("\n").join([c.to_str() for c in self.children])
        proc_body = self.indent(proc_body,4,' ')

        cur_vars = list(dict.fromkeys(cur_vars))

        proc_return_value = [("_" if i[0].isupper() else "") + i[0] for i in self.proc_return_type]
        proc_return_value = ", ".join(proc_return_value)
        
        if len(self.proc_return_type) > 1:
            proc_return_value = "(" + proc_return_value + ")"
        elif len(self.proc_return_type) == 0:
            proc_return_value = "()"
            
        proc_return_value += ";"

        s = """proc {proc_name}({proc_args}) : {proc_return_type} = {{ 
{proc_return_value_decl}
{proc_body}
    return {proc_return_value}
}}""".format(proc_name = self.proc_name
             , proc_args = (", ").join([i[0] + ": uint256" for i in self.proc_args])
             , proc_return_type = "(" + rett + ")" if rett != "" else "unit"
             , proc_return_value = proc_return_value
             , proc_return_value_decl = ("    var " if cur_vars else "") + ", ".join(i for i in cur_vars) + (";" if cur_vars else "")
             , proc_body = proc_body )
        return s


    def setProcName(self,name):
        self.proc_name = ("_" if name[0].isupper() else "")  + name

class YulEasyCryptListener(YulListener):
    def __init__(self, *args, **kwargs):
        super(YulEasyCryptListener, self).__init__(*args, **kwargs)
        self.ec_node = RootNode("root")
        self.root_node = self.ec_node
        
        self.main_proc = ProcNode("main",parent = self.root_node)
        self.main_proc.proc_name = "main"
        
        self.nonce = 0
        self.proc_list = []

    def set_main_if_orphan(self):
        pass
        # if (self.ec_node.find_parent_proc(self.ec_node) == None):
        #     self.ec_node >> self.main_proc
        #     self.ec_node = self.main_proc

        



    # Enter a parse tree produced by YulParser#start.
    def enterStart(self, ctx:YulParser.StartContext):
        pass

    # Exit a parse tree produced by YulParser#start.
    def exitStart(self, ctx:YulParser.StartContext):
        pass
        #self.built_string += "],"

    # Enter a parse tree produced by YulParser#yul_object.
    def enterYul_object(self, ctx:YulParser.Yul_objectContext):
        pass
        #self.built_string += "module YulExtract = {"

    # Exit a parse tree produced by YulParser#yul_object.
    def exitYul_object(self, ctx:YulParser.Yul_objectContext):
        pass
        #self.built_string += "\n}."

    # Enter a parse tree produced by YulParser#yul_code.
    def enterYul_code(self, ctx:YulParser.Yul_codeContext):
        pass


    # Exit a parse tree produced by YulParser#yul_code.
    def exitYul_code(self, ctx:YulParser.Yul_codeContext):
        pass

    # Enter a parse tree produced by YulParser#yul_if.
    def enterYul_if(self, ctx:YulParser.Yul_ifContext):
        ifnode = IfNode("if" + str(self.nonce), parent = self.ec_node)
        self.ec_node = ifnode
        self.nonce += 1


    # Exit a parse tree produced by YulParser#yul_if.
    def exitYul_if(self, ctx:YulParser.Yul_ifContext):
        self.ec_node = self.ec_node.parent
        

    # Enter a parse tree produced by YulParser#yul_switch.
    def enterYul_switch(self, ctx:YulParser.Yul_switchContext):
        swnode = SwitchNode("switch" + str(self.nonce), parent = self.ec_node)
        self.ec_node = swnode
        self.nonce += 1


    # Exit a parse tree produced by YulParser#yul_switch.
    def exitYul_switch(self, ctx:YulParser.Yul_switchContext):
        self.ec_node = self.ec_node.parent

    # Enter a parse tree produced by YulParser#yul_case.
    def enterYul_case(self, ctx:YulParser.Yul_caseContext):
        case_node = CaseNode("case" + str(self.nonce), parent = self.ec_node)
        self.ec_node = case_node
        self.nonce += 1

    # Exit a parse tree produced by YulParser#yul_case.
    def exitYul_case(self, ctx:YulParser.Yul_caseContext):
        self.ec_node = self.ec_node.parent

    # Enter a parse tree produced by YulParser#yul_default.
    def enterYul_default(self, ctx:YulParser.Yul_defaultContext):
        block_node = BlockNode("block" + str(self.nonce), parent = self.ec_node)
        self.nonce += 1
        self.ec_node = block_node

    # Exit a parse tree produced by YulParser#yul_default.
    def exitYul_default(self, ctx:YulParser.Yul_defaultContext):
        self.ec_node = self.ec_node.parent

    # Enter a parse tree produced by YulParser#yul_for_loop.
    def enterYul_for_loop(self, ctx:YulParser.Yul_for_loopContext):
        for_loop = ForNode("for" + str(self.nonce), parent = self.ec_node)
        self.nonce += 1
        self.ec_node = for_loop

    # Exit a parse tree produced by YulParser#yul_for_loop.
    def exitYul_for_loop(self, ctx:YulParser.Yul_for_loopContext):
        self.ec_node = self.ec_node.parent

    # Enter a parse tree produced by YulParser#yul_break.
    def enterYul_break(self, ctx:YulParser.Yul_breakContext):
        pass

    # Exit a parse tree produced by YulParser#yul_break.
    def exitYul_break(self, ctx:YulParser.Yul_breakContext):
        pass

    # Enter a parse tree produced by YulParser#yul_continue.
    def enterYul_continue(self, ctx:YulParser.Yul_continueContext):
        pass

    # Exit a parse tree produced by YulParser#yul_continue.
    def exitYul_continue(self, ctx:YulParser.Yul_continueContext):
        pass
        #self.built_string += "],"

    # Enter a parse tree produced by YulParser#yul_leave.
    def enterYul_leave(self, ctx:YulParser.Yul_leaveContext):
        pass

    # Exit a parse tree produced by YulParser#yul_leave.
    def exitYul_leave(self, ctx:YulParser.Yul_leaveContext):
        pass


    # Enter a parse tree produced by YulParser#yul_function_definition.
    def enterYul_function_definition(self, ctx:YulParser.Yul_function_definitionContext):
        proc = ProcNode("proc" + str(self.nonce)) 
        proc.setProcName(ctx.getChild(1).getText())
        self.proc_list.append(proc.proc_name)
        
        self.ec_node >> proc
        self.ec_node = proc
        self.nonce += 1


    # Exit a parse tree produced by YulParser#yul_function_definition.
    def exitYul_function_definition(self, ctx:YulParser.Yul_function_definitionContext):
        self.ec_node = self.ec_node.parent
        #self.ec_node.show()

    # Enter a parse tree produced by YulParser#yul_variable_declaration.
    def enterYul_variable_declaration(self, ctx:YulParser.Yul_variable_declarationContext):
        self.ec_node = VarDeclNode("var" + str(self.nonce), parent = self.ec_node)

    # Exit a parse tree produced by YulParser#yul_variable_declaration.
    def exitYul_variable_declaration(self, ctx:YulParser.Yul_variable_declarationContext):
        self.ec_node = self.ec_node.parent

    # Enter a parse tree produced by YulParser#yul_function_arg_list.
    def enterYul_function_arg_list(self, ctx:YulParser.Yul_function_arg_listContext):
        pass
        #print(ctx.getChild(0).getChild(3).getText())
        #self.built_string += "("

    # Exit a parse tree produced by YulParser#yul_function_arg_list.
    def exitYul_function_arg_list(self, ctx:YulParser.Yul_function_arg_listContext):
        pass
        #self.built_string += ")"

        #self.built_string += "],"

    # Enter a parse tree produced by YulParser#yul_function_ret_list.
    def enterYul_function_ret_list(self, ctx:YulParser.Yul_function_ret_listContext):
        pass
        # if ctx.getChildCount() == 1 :
        #     self.built_string += ": uint256"
        # else:
        #     self.built_string += ": unit"

        # self.built_string += " = {\n"    
        

    # Exit a parse tree produced by YulParser#yul_function_ret_list.
    def exitYul_function_ret_list(self, ctx:YulParser.Yul_function_ret_listContext):
        pass

    # Enter a parse tree produced by YulParser#yul_typed_identifier_list.
    def enterYul_typed_identifier_list(self, ctx:YulParser.Yul_typed_identifier_listContext):
        pass

    # Exit a parse tree produced by YulParser#yul_typed_identifier_list.
    def exitYul_typed_identifier_list(self, ctx:YulParser.Yul_typed_identifier_listContext):
        pass

    # Enter a parse tree produced by YulParser#yul_identifier_list.
    def enterYul_identifier_list(self, ctx:YulParser.Yul_identifier_listContext):
        pass

    # Exit a parse tree produced by YulParser#yul_identifier_list.
    def exitYul_identifier_list(self, ctx:YulParser.Yul_identifier_listContext):
        pass
        #self.built_string += "],"

    # Enter a parse tree produced by YulParser#yul_block.
    def enterYul_block(self, ctx:YulParser.Yul_blockContext):
        block_node = BlockNode("block" + str(self.nonce), parent = self.ec_node)
        self.nonce += 1
        self.ec_node = block_node

    # Exit a parse tree produced by YulParser#yul_block.
    def exitYul_block(self, ctx:YulParser.Yul_blockContext):
        self.ec_node = self.ec_node.parent

    # Enter a parse tree produced by YulParser#yul_statement.
    def enterYul_statement(self, ctx:YulParser.Yul_statementContext):
        pass
        # self.built_string += "[\"yul_statement\","

    # Exit a parse tree produced by YulParser#yul_statement.
    def exitYul_statement(self, ctx:YulParser.Yul_statementContext):
        pass
        #self.built_string += "],"

    # Enter a parse tree produced by YulParser#yul_assignment.
    def enterYul_assignment(self, ctx:YulParser.Yul_assignmentContext):
        self.ec_node = AssNode("ass" + str(self.nonce), parent = self.ec_node)

        #self.built_string += ctx.getChild(0).getText() + " <- "

    # Exit a parse tree produced by YulParser#yul_assignment.
    def exitYul_assignment(self, ctx:YulParser.Yul_assignmentContext):
        self.ec_node = self.ec_node.parent
        #self.built_string += "],"

    # Enter a parse tree produced by YulParser#yul_expression.
    def enterYul_expression(self, ctx:YulParser.Yul_expressionContext):
        expr_node = ExpressionNode("expr" + str(self.nonce), parent = self.ec_node)
        self.nonce += 1
        self.ec_node = expr_node


    # Exit a parse tree produced by YulParser#yul_expression.
    def exitYul_expression(self, ctx:YulParser.Yul_expressionContext):
        self.ec_node = self.ec_node.parent


    # Enter a parse tree produced by YulParser#yul_function_call.
    def enterYul_function_call(self, ctx:YulParser.Yul_function_callContext):
        self.set_main_if_orphan()        
        curr_node = FunctionCallNode("func" + str(self.nonce), parent = self.ec_node)
        self.nonce += 1
        if ctx.parentCtx.parentCtx.getRuleIndex() == YulParser.RULE_yul_assignment or ctx.parentCtx.parentCtx.getRuleIndex() == YulParser.RULE_yul_variable_declaration :
            self.ec_node.parent.rhs = curr_node
            curr_node.ass_child = True
        self.ec_node = curr_node
        self.ec_node.setFunctionCallName(ctx.getChild(0).getText())


    # Exit a parse tree produced by YulParser#yul_function_call.
    def exitYul_function_call(self, ctx:YulParser.Yul_function_callContext):
        self.ec_node = self.ec_node.parent

    # Enter a parse tree produced by YulParser#yul_literal.
    def enterYul_literal(self, ctx:YulParser.Yul_literalContext):
        cur_node = LiteralNode("literal" + str(self.nonce), parent = self.ec_node)
        self.nonce += 1
        if ctx.parentCtx.parentCtx.getRuleIndex() == YulParser.RULE_yul_assignment or ctx.parentCtx.parentCtx.getRuleIndex() == YulParser.RULE_yul_variable_declaration:
            self.ec_node.parent.rhs = cur_node
        self.ec_node = cur_node

        #self.built_string += ctx.getText()

    # Exit a parse tree produced by YulParser#yul_literal.
    def exitYul_literal(self, ctx:YulParser.Yul_literalContext):
        self.ec_node = self.ec_node.parent

    # Enter a parse tree produced by YulParser#yul_number_literal.
    def enterYul_number_literal(self, ctx:YulParser.Yul_number_literalContext):
        pass
        #self.built_string += "[\"yul_number_literal\","

    # Exit a parse tree produced by YulParser#yul_number_literal.
    def exitYul_number_literal(self, ctx:YulParser.Yul_number_literalContext):
        self.ec_node.setLiteralValue("!" + ctx.getText())

    # Enter a parse tree produced by YulParser#yul_true_literal.
    def enterYul_true_literal(self, ctx:YulParser.Yul_true_literalContext):
        pass
    # Exit a parse tree produced by YulParser#yul_true_literal.
    def exitYul_true_literal(self, ctx:YulParser.Yul_true_literalContext):
        pass

    # Enter a parse tree produced by YulParser#yul_false_literal.
    def enterYul_false_literal(self, ctx:YulParser.Yul_false_literalContext):
        pass
    # Exit a parse tree produced by YulParser#yul_false_literal.
    def exitYul_false_literal(self, ctx:YulParser.Yul_false_literalContext):
        pass

    # Enter a parse tree produced by YulParser#yul_hex_number.
    def enterYul_hex_number(self, ctx:YulParser.Yul_hex_numberContext):
        self.ec_node.setLiteralValue("!" + str (int(ctx.getText(), 16)))

    # Exit a parse tree produced by YulParser#yul_hex_number.
    def exitYul_hex_number(self, ctx:YulParser.Yul_hex_numberContext):
        pass

    # Enter a parse tree produced by YulParser#yul_dec_number.
    def enterYul_dec_number(self, ctx:YulParser.Yul_dec_numberContext):
        pass
        #self.built_string += "[\"yul_dec_number\",\"{}\",],".format(ctx.DEC_NUMBER())
    # Exit a parse tree produced by YulParser#yul_dec_number.
    def exitYul_dec_number(self, ctx:YulParser.Yul_dec_numberContext):
        pass

    # Enter a parse tree produced by YulParser#yul_type_name.
    def enterYul_type_name(self, ctx:YulParser.Yul_type_nameContext):
        pass
        #self.built_string += "[\"yul_type_name\",\"{}\",],".format(ctx.ID_LITERAL())

    # Exit a parse tree produced by YulParser#yul_type_name.
    def exitYul_type_name(self, ctx:YulParser.Yul_type_nameContext):
        pass

    # Enter a parse tree produced by YulParser#yul_identifier.
    def enterYul_identifier(self, ctx:YulParser.Yul_identifierContext):
        
        if (ctx.parentCtx.parentCtx.getRuleIndex() == YulParser.RULE_yul_function_arg_list):
            self.ec_node.proc_args.append((ctx.getText(), None))
            return
        if (ctx.parentCtx.parentCtx.getRuleIndex() == YulParser.RULE_yul_function_ret_list):
            self.ec_node.proc_return_type.append((ctx.getText(), None))
            return
        if (ctx.parentCtx.parentCtx.getRuleIndex() == YulParser.RULE_yul_assignment):
            if ctx.parentCtx.getRuleIndex() == YulParser.RULE_yul_expression:
                self.ec_node.parent.rhs.setLiteralValue(ctx.getText())
            else:
                self.ec_node.lhs.append(("_" if ctx.getText()[0].isupper() else "") + ctx.getText())

            return
        if (ctx.parentCtx.parentCtx.getRuleIndex() == YulParser.RULE_yul_variable_declaration):
            if ctx.parentCtx.getRuleIndex() == YulParser.RULE_yul_expression:
                self.ec_node.parent.rhs.setLiteralValue(ctx.getText())
            else:
                self.ec_node.lhs.append(("_" if ctx.getText()[0].isupper() else "") + ctx.getText())
            return
        if (ctx.parentCtx.getRuleIndex() == YulParser.RULE_yul_expression):
            curr_node = IdentifierNode("id" + str(self.nonce), parent = self.ec_node)
            curr_node.id_value = ctx.getText()
            self.nonce += 1
            return

    # Exit a parse tree produced by YulParser#yul_identifier.
    def exitYul_identifier(self, ctx:YulParser.Yul_identifierContext):
        pass

    # Enter a parse tree produced by YulParser#yul_string_literal.
    def enterYul_string_literal(self, ctx:YulParser.Yul_string_literalContext):
        if (ctx.parentCtx.getRuleIndex() != YulParser.RULE_yul_object):        
            self.ec_node.root.str_constants.append(ctx.getText().strip('"'))
            self.ec_node.setLiteralValue(ctx.getText().strip('"'))
        
    # Exit a parse tree produced by YulParser#yul_string_literal.
    def exitYul_string_literal(self, ctx:YulParser.Yul_string_literalContext):
        pass
