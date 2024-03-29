############################################################
# CMPSC 442: Logic
############################################################

import copy
import itertools


student_name = "Michael Sullivan"

############################################################
# Imports
############################################################

# Include your imports here, if any are used.



############################################################
# Section 1: Propositional Logic
############################################################

class Expr(object):
    def __hash__(self):
        return hash((type(self).__name__, self.hashable))

class Atom(Expr):
    def __init__(self, name):
        self.name = name
        self.hashable = self.name
    def __eq__(self, other):
        return (type(self) == type(other)) and self.name == other.name
    def __repr__(self):
        return f"Atom({self.name})"
    def __hash__(self):
        return hash(self.name)
    def atom_names(self):
        return set(self.name)
    def evaluate(self, assignment):
        return assignment[self.name]
    def to_cnf(self):
        return self

class Not(Expr):
    def __init__(self, arg):
        self.arg = arg
        self.hashable = arg
    def __eq__(self, other):
        return type(self) == type(other) and self.arg.name == other.arg.name

    def __repr__(self):
        return f"Not({self.arg})"
    def __hash__(self):
        return hash(self.hashable)
    def atom_names(self):
        return self.arg.atom_names()
    def evaluate(self, assignment):
        return not self.arg.evaluate(assignment)
    def to_cnf(self):
        cnf_arg = self.arg.to_cnf()
        if isinstance(cnf_arg, And):
            return Or(*[Not(i).to_cnf() for i in cnf_arg.hashable]).to_cnf()
        
        elif isinstance(cnf_arg, Or):
            return And(*[Not(i).to_cnf() for i in cnf_arg.hashable]).to_cnf()
            

        elif isinstance(cnf_arg, Not):
            return cnf_arg.arg
        else:
            return Not(self.arg)
        
        
class And(Expr):
    def __init__(self, *conjuncts):
        self.conjuncts = frozenset(conjuncts)
        self.hashable = self.conjuncts
    def __eq__(self, other):
        return isinstance(other, And) and self.conjuncts == other.conjuncts
    def __repr__(self):
        return "And(" + ", ".join(str(conjunct) for conjunct in self.conjuncts) + ")"
    def __hash__(self):
        return hash(self.hashable)
    def atom_names(self):
        names = []
        for i in self.conjuncts:
            names.extend(i.atom_names())
        return set(names)
    def evaluate(self, assignment):
        for i in list(self.conjuncts):
            if not i.evaluate(assignment):
                return False
        return True

    def to_cnf(self):
        conjuncts = []
        if len(self.hashable) == 1:
            return list(self.hashable)[0]
        for i in self.hashable:
            i = i.to_cnf()
            if isinstance(i, And):
                for j in i.conjuncts:
                    conjuncts.append(j)
            else:
                conjuncts.append(i.to_cnf())

        if all(isinstance(conjunct, Or) for conjunct in conjuncts):
            conjuncts.sort(key=lambda x: len(x.hashable))
            filtered_conjuncts = []
            for i in conjuncts:
                if not any(j.hashable.issubset(i.hashable) for j in conjuncts if i != j):
                    filtered_conjuncts.append(i)
    
            conjuncts = filtered_conjuncts

        
       
        return And(*conjuncts)

class Or(Expr):
    def __init__(self, *disjuncts):
        self.disjuncts = frozenset(disjuncts)
        self.hashable = self.disjuncts
    def __eq__(self, other):
        return isinstance(other, Or) and self.disjuncts == other.disjuncts
            
    def __repr__(self):
        return "Or(" + ", ".join(str(disjunct) for disjunct in self.disjuncts) + ")"
    def __hash__(self):
        return hash(self.hashable)
    def atom_names(self):
        names = []
        for i in self.disjuncts:
            names.extend(i.atom_names())
        return set(names)
    def evaluate(self, assignment):
        for i in list(self.disjuncts):
            if i.evaluate(assignment):
                return True
        return False
    
    def get_conjuncts(self, con):
        ret = []
        if isinstance(con, Or):
            for j in con.disjuncts:
                ret.append(j)
            else:
                ret.append(con)
        return ret
    
    def to_cnf(self):
        disjuncts = []
        and_seen = None
        #deprication candidate
        if len(self.disjuncts) == 1:
            return list(self.disjuncts)[0]

        for i in self.hashable:
            i = i.to_cnf()
            if isinstance(i, Or):
                disjuncts.extend(list(i.hashable))
            elif isinstance(i, And) and not and_seen:
                and_seen = i
            else:
                disjuncts.append(i.to_cnf())
        
        if and_seen:
            return And(*[Or(*(disjuncts + [j])).to_cnf() for j in and_seen.hashable]).to_cnf()
        else:
            return Or(*disjuncts)#check
        



        
       
class Implies(Expr):
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.hashable = (left, right)
    def __eq__(self, other):
        return isinstance(other, Implies) and self.left == other.left and self.right == other.right
    def __repr__(self):
        return f"Implies({self.left}, {self.right})"
    def __hash__(self):
        return hash(self.hashable)
    def atom_names(self):
        return self.left.atom_names().union(self.right.atom_names())
    def evaluate(self, assignment):
        left_evaluate = self.left.evaluate(assignment)
        right_evaluate = self.right.evaluate(assignment)
        
        if left_evaluate and not right_evaluate:
            return False
        return True
    def to_cnf(self):
        expr = Or(Not(self.hashable[0]).to_cnf(), self.hashable[1].to_cnf()).to_cnf()
        count = 0
        while not is_cnf(expr):
            if count == 5:
                return expr
            expr = expr.to_cnf()
            count += 1
        return expr
        

class Iff(Expr):
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.hashable = (left, right)
    def __eq__(self, other):
        return isinstance(other, Iff) and self.left == other.left and self.right == other.right
            
    def __repr__(self):
        return f"Iff({self.left}, {self.right})"
    def __hash__(self):
        return hash(self.hashable)
    def atom_names(self):
        return self.left.atom_names().union(self.right.atom_names())
    def evaluate(self, assignment):
        left_evaluate = self.left.evaluate(assignment)
        right_evaluate = self.right.evaluate(assignment)
        return left_evaluate == right_evaluate
    def to_cnf(self):
        expr = And(Implies(self.hashable[0], self.hashable[1]).to_cnf(), Implies(self.hashable[1], self.hashable[0]).to_cnf())
        count = 0
        while not is_cnf(expr):
            if count == 5:
                return expr
            expr = expr.to_cnf()
            count += 1
        return expr
      


def satisfying_assignments(expr):
    items = expr.atom_names()
    combinations = itertools.product([True, False], repeat=len(items))
    assignments = list(dict(zip(items, combo)) for combo in combinations)
    satisfying = []
    for ass in assignments:
        if expr.evaluate(ass):
            satisfying.append(ass)
            yield ass



def get_atoms(expr):
    if isinstance(expr, Atom):
        return [expr.name]
    ret = []
    items = list(expr.hashable)
    for i in items:
        if not isinstance(i, Atom):
            ret.extend(get_atoms(i))
        else:
            ret.append(i.name)
    return ret
    
        
def is_cnf(expr):
    if isinstance(expr, Atom) or isinstance(expr, Not):
        return True
    elif isinstance(expr, Or):
        for disjunct in expr.disjuncts:
            if not (isinstance(disjunct, Not) or isinstance(disjunct, Atom)):
                return False
        return True
    elif isinstance(expr, And):
        for conjunct in expr.conjuncts:
            if not (isinstance(conjunct, Or) or (isinstance(conjunct, Atom) or isinstance(conjunct, Not) and is_cnf(conjunct))):
                return False
        return True
    else:
        return False


class KnowledgeBase(object):
    def __init__(self):
        self.fact_set = set()
        self.changed = False
    def get_facts(self):
        return self.fact_set

    def tell(self, expr):
        expr = expr.to_cnf()
        if isinstance(expr, And):
            for i in expr.hashable:
                self.fact_set.add(i)
        else:
            self.fact_set.add(expr)

    def compliments(self, i, j):
        i, j = i.to_cnf(), j.to_cnf()
        if i == Not(j).to_cnf():
            return True
        else:
            return False
        
    def pl_return(self, include_set):
        if len(include_set) == 1:
            return set(include_set).pop()
        elif len(include_set) > 1:
            return Or(*include_set)
        else:
            return None

    def pl_resolve(self, ci, cj):
        self.changed = False
        ci, cj = ci.to_cnf(), cj.to_cnf()
        resolved = set()
        if isinstance(ci, Or) and isinstance(cj, Or):
            for i in ci.hashable:
                for j in cj.hashable:
                    if self.compliments(i, j):
                        self.changed = True
                        include = self.pl_return(set(ci.hashable).union(set(cj.hashable)) - {i, j})
                        if include:
                            resolved.add(include)

        elif (isinstance(ci, Or)):
            for i in ci.hashable:
                if self.compliments(i, cj):
                    self.changed = True
                    include = self.pl_return(ci.hashable - {i})
                    if include:
                        resolved.add(include)


        elif (isinstance(cj, Or)):
            for j in cj.hashable:
                if self.compliments(j, ci):
                    self.changed = True
                    include = self.pl_return(cj.hashable - {j})
                    if include:
                        resolved.add(include)

        elif (isinstance(ci, Not) or isinstance(ci, Atom)) and (isinstance(cj, Not) or isinstance(cj, Atom)):
            if self.compliments(ci, cj):
                self.changed = True

        return resolved
    
    def get_disjuncts(self, item):
        disjuncts = set()
        if isinstance(item, Or):
            for i in item.hashable:
                disjuncts.add(i)
        else:
            disjuncts.add(item)
        return disjuncts
    
    def ask(self, expr):
        rep = And(And(*self.fact_set).to_cnf(), Not(expr).to_cnf()).to_cnf()
        expr = expr.to_cnf()
        new = set()
        clauses = set(rep.hashable)
        print(clauses)
        while True:
            for clause1 in clauses:
                for clause2 in clauses:
                    resolve = set()
                    if not clause1 == clause2:
                        resolve = self.pl_resolve(clause1, clause2)
                        if not self.changed:
                            continue
                        elif len(resolve)==0:
                            return True
                        #for all potential resolutions, if one of them is a resolved or, conduct additional resolution
                        
                        else:
                            remove = set()
                            for i in resolve:
                                if isinstance(i, Or):
                                    for x in i.disjuncts:
                                        for y in i.disjuncts:
                                            
                                            if x != y:
                                                if self.compliments(x,y):
                                                    remove.add(i)
                                                    break
                            for i in remove:
                                resolve.remove(i)
                                
                        new=new.union(resolve)
                                                  
            if new.issubset(clauses):
                return False
            clauses = clauses.union(new)
                    




############################################################
# Section 2: Logic Puzzles
############################################################

# Puzzle 1

# Populate the knowledge base using statements of the form kb1.tell(...)
kb1 = KnowledgeBase()
kb1.tell(Implies(Or(Not(Atom("mortal")),Atom("mammal")),Atom("horned")))
kb1.tell(Implies(Atom("mythical"),Not(Atom("mortal"))))
kb1.tell(Implies(Not(Atom("mythical")),And(Atom("mortal"),Atom("mammal"))))
kb1.tell(Implies(Atom("horned"),Atom("magical")))

# Write an Expr for each query that should be asked of the knowledge base
mythical_query = Atom("mythical")
magical_query = Atom("magical")
horned_query = Atom("horned")
# Record your answers as True or False; if you wish to use the above queries,
# they should not be run when this file is loaded
is_mythical = False
is_magical = True
is_horned = True

# Puzzle 2

# Write an Expr of the form And(...) encoding the constraints
party_constraints = And(Implies(Or(Atom("a"),Atom("m")),Atom("j")),Implies(Not(Atom("m")),Atom("a")),Implies(Atom("a"),Not(Atom("j"))))


# Compute a list of the valid attendance scenarios using a call to
#print(list(satisfying_assignments(party_constraints)))
# satisfying_assignments(expr)
valid_scenarios = [{'m': True, 'j': True, 'a': False}]

# Write your answer to the question in the assignment
puzzle_2_question = """
The only possible way that guests can come to this event is if mary and john come, however ann does not come.
"""

# Puzzle 3

# Populate the knowledge base using statements of the form kb3.tell(...)
kb3 = KnowledgeBase()
p1 = Atom("p1")
e1 = Atom("e1") 
p2 = Atom("p2") 
e2 = Atom("e2") 
s1 = Atom("s1") 
s2 = Atom("s2")
kb3.tell(Iff(p1, Not(e1)))
kb3.tell(Iff(p2, Not(e2)))
kb3.tell(Iff(And(p1, e2), s1))
kb3.tell(Iff(Or(And(p1, e2), And(p2, e1)), s2))
kb3.tell(And(Or(Not(s1), Not(s2)), Or(s1, s2)))
puzzle_3_question = """
Based on the following queries, It can be true that the first room is empty, the second room is full, and the secon sign is accurate.
The quereis that I made were the iff relationships with the e and p varoables. The iff relationships with what each sign implied, and the and relationship
representing that only one sign is true.
"""

# Puzzle 4

# Populate the knowledge base using statements of the form kb4.tell(...)

kb4 = KnowledgeBase()
ia = Atom("ia")
ib = Atom("ib") 
ic = Atom("ic") 
kc = Atom("kc") 
ka = Atom("ka") 
kb = Atom("kb")
kb4.tell(Implies(ia, And(kb, Not(kc))))
kb4.tell(Implies(ib, Not(kb)))
kb4.tell(Implies(ic, And(ka, kb)))
kb4.tell(Iff(ia,Or(Not(ib),Not(ic))))
kb4.tell(Iff(ib,Or(Not(ia),Not(ic))))
kb4.tell(Iff(ic,Or(Not(ia),Not(ib))))
#a = And(Iff(ia,Or(Not(ib),Not(ic))).to_cnf(),Iff(ib,Or(Not(ia),Not(ic))).to_cnf(),Iff(ic,Or(Not(ia),Not(ib))).to_cnf())
#print(a.to_cnf())
"""
print(kb4.ask(ia))
print(kb4.ask(ib))
print(kb4.ask(ic))
"""



# Uncomment the line corresponding to the guilty suspect
# guilty_suspect = "Adams"
guilty_suspect = "Brown"
# guilty_suspect = "Clark"

# Describe the queries you made to ascertain your findings
puzzle_4_question = """
The queries that i made were the relationship that only one suspect can be guilty, also that clark doesnt know him and brown does. I also specified the implications of each individual 
beign innocent.
"""


