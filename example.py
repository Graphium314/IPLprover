from IPLprover import *
p = prover()
print(p.proof('((A)->((B)->((A)/\(B))))'))
print(p.proof('(~(~((A)\/(~(A)))))'))
print(p.proof('(((A)->((C)\\/(D)))->(((B)->((C)\\/(D)))->(((C)->((E)\\/(F)))->(((D)->((E)\\/(F)))->(((E)->(G))->(((F)->(G))->(((A)\\/(B))->(G))))))))'))
