from CvxAlgGeo import *

## Initial settings ##
n = 3			# Number of variables
d = 4			# Maximum degree of polynomials
m = 2			# Number of constraints
num_monos = 4	# Max number of monomials
R = PolynomialRing(RR, 'x', n)
X = R.gens();

##########################################

Prg = []
Cns = []

f = R.random_element(d, randint(1, num_monos)) + sum(p^d for p in X)
Prg.append(f)

for i in range(m):
    g = R.random_element(d, num_monos)
    Cns.append(g)

Prg.append(Cns)

conf = {'Details':False, 'AutoMatrix':True}
M = identity_matrix(QQ, m+1)

print Prg

GP = geometric.GPTools(Prg, R, H=M, Settings=conf)
GP.minimize()

print GP.Info
SOS = semidefinite.SosTools(Prg, R, Settings=conf)
SOS.init_sdp()
SOS.minimize()
print SOS.Info
