from sympy import factorint, n_order, primitive_root
from sympy.ntheory.modular import crt
from math import gcd
def lift_pair_prime_power(p,k):
    # consecutive pair mod p^k with equal orders = phi(p^k): consecutive primitive roots mod p, lifted
    M=p**k; phi=(p-1)*p**(k-1)
    for y in range(1,M-1):
        if gcd(y,p)==1 and gcd(y+1,p)==1 and n_order(y,M)==phi and n_order(y+1,M)==phi: return y,M
    return None
def seven_lift(b):
    M=7**b
    for y in range(3,M,7):   # y ≡ 3 mod 7: want ord(y)=6*7^(b-1), ord(y+1)=3*7^(b-1)
        if n_order(y,M)==6*7**(b-1) and n_order(y+1,M)==3*7**(b-1): return y,M
def construct(m):
    f=factorint(m); res=[];mods=[]
    a=f.get(3,0); b=f.get(7,0)
    if a: res.append(4%3**a); mods.append(3**a)
    if b: y,M=seven_lift(b); res.append(y); mods.append(M)
    for p,k in f.items():
        if p in (3,7): continue
        y,M=lift_pair_prime_power(p,k); res.append(y); mods.append(M)
    x=int(crt(mods,res)[0]); return x
bad=[]
for m in range(3,30001,2):
    f=factorint(m)
    if len(f)==1 and list(f)[0] in (3,7): continue   # pure powers: excluded
    x=construct(m)
    ok = gcd(x,m)==1 and gcd(x+1,m)==1 and n_order(x,m)==n_order(x+1,m)
    if not ok: bad.append(m)
print("construction failures up to 30000:",bad[:20],len(bad))
# pure powers: confirm f=0 cheaply for small cases
def f(m): return sum(1 for x in range(1,m) if gcd(x,m)==1 and gcd(x+1,m)==1 and n_order(x,m)==n_order(x+1,m))
print("f(3^a):",[f(3**a) for a in range(1,7)],"f(7^b):",[f(7**b) for b in range(1,4)])
