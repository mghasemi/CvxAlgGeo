#******************************************************************************#
#       Copyright (C) 2011-2013 Mehdi Ghasemi <mehdi.ghasemi@usask.ca>         #
#                                                                              #
#  Distributed under the terms of the GNU General Public License (GPL)         #
#  as published by the Free Software Foundation; either version 2 of           #
#  the License, or (at your option) any later version                          #
#                  http://www.gnu.org/licenses/                                #
#******************************************************************************#

from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.real_mpfr import *
from sage.matrix.constructor import Matrix

class SosTools:
    """
    SosTools class:
        Performs sums of squares related computations on real 
	multivariate polynomials.
	
	Current version solves the following problems:
		
		Computing the lower bound of a polynomial f over the
		semialgebraic set defined by g1>=0,..., gm>=0, using
		Lasserre's semidefinite relaxation method of a given 
		order.
		
		Extracting a SOS decomposition of a given real polynomial,
		if such a decomposition exists
    """
    
    MainPolynomial = 0
    Ring = []
    NumVars = 1
    vars = []
    Relaxation = 1
    NumberOfConstraints = 1
    Constraints = []
    HalfDegs = []
    Degs = []
    Matrices = None
    Ord = 0
    Monomials = []
    f_min = 0
    precision = 5
    MatSize = []
    solver = 'cvxopt'
    
    def __init__(self, Prog, Rng, Settings = {'Order':0, 'Solver':'cvxopt', 'Iterations':100, 'detail':True, 'tryKKT':0}):
        """
        Initiates a SosTools object by input data, mainly polynomials
        f and g1,..., gm
        
        Arguments:
	    Prog:
	        is the list of polynomials f, g_1,..., gm, in the following
	        format:
	                [f, [g1,..., gm]]
	
	    Rng:
	        is the polynomial ring were f, g1,..., gm are coming from.
	        A typical format is:
	               PolynomialRing(base, 'x', n)
	        where 
	        base is the base ring, such as 
	            RR: Real numbers,
	            QQ: Rational numbers
	            ZZ: Integers
	            etc,
	        'x' is a generic name for indeterminate, and
	         n is the number of indeterminates.
	
	    Settings:
	        is a dictionary of options to configure the behavior of the
	        object as well as sdp solver.
	        The options are:
	
	        Order:
	            The order of sdp relaxation is (the ceiling of
	            half degree of f, g1,..., gm) + Order. 
	        Solver:
	            'cvxopt',
	            'csdp',
	            'sdpa'.
	            by default is set to 'cvxopt', but based on available
	            sdp solvers can be chaned to 'csdp' and 'sdpa'.
	        Iterations:
	            The maximum number of iterations of the solver. The
	            default value is 100, and it currently just effects 
	            'cvxopt' solver.
	        detail:
	            Boolean value, default is True. Set to False to hide
                    the sdp solver's progress output. Only works for 'cvxopt'.
	        tryKKT:
	            A positive integer number. If the solver encounters a
	            singular KKT matrix, it continues to iterate for this 
	            given number of iterations. Only works for 'cvxopt'.
        """
                
        self.MainPolynomial = Prog[0]
        self.Field = self.MainPolynomial.base_ring()
        self.Ring = Rng
        self.vars = self.Ring.gens()
        self.NumVars = len(self.vars)
        ###
        f_tot_deg = self.MainPolynomial.total_degree()
        if (f_tot_deg % 2) == 1:
            f_half_deg = (f_tot_deg + 1)/2
        else:
            f_half_deg = f_tot_deg/2
        
        self.MainPolyHlfDeg = f_half_deg
        self.MainPolyTotDeg = f_tot_deg
        ###
        self.Constraints = []
        if len(Prog) > 1:
            self.Constraints = Prog[1]
        self.Constraints.append(self.vars[0]**0)
        self.NumberOfConstraints = len(self.Constraints)
        ###
        for g in self.Constraints:
            tmp_deg = g.total_degree()
            self.Degs.append(tmp_deg)
            if (tmp_deg % 2) == 1:
                self.HalfDegs.append((tmp_deg+1)/2)
            else:
                self.HalfDegs.append(tmp_deg/2)
        ###
        if 'Order' in Settings:
            self.Ord = Settings['Order']
        else:
            self.Ord = 0
        ###
        if 'Solver' in Settings:
            self.solver = Settings['Solver']
        else:
            self.solver = 'cvxopt'
        ###
        if 'detail' in Settings:
            self.detail = Settings['detail']
        else:
            self.detail = True
        ###
        if len(self.HalfDegs) > 0 :
            cns_half_deg_max = max(self.HalfDegs)
        else:
            cns_half_deg_max = 0
        self.Relaxation = max(self.Relaxation,f_half_deg,cns_half_deg_max)+self.Ord;
        ###
        self.Monomials = self.MonomialsVec(2*self.Relaxation)
        self.Info = {'min':0, 'CPU':0, 'Wall':0, 'status':'Unknown', 'Message':'', 'is sos':False};

        
    def NumMonomials(self, n, d):
        """
        Returns the dimension of the space of polynomials 
        on n variable with degree at most d.
        """
        from math import factorial
        return factorial(n+d)/(factorial(n)*factorial(d))
            
    def MonomialsVec(self, deg):
        """
        Returns a vector consists of all monomials of degree up to deg
        """
        
        f1 = (1 + sum(p for p in self.vars))**deg
        vec = f1.monomials()
        vec.reverse()
        return vec
        
    def PolyCoefFullVec(self):
        c=[]
        fmono = self.MainPolynomial.monomials()
        fcoef = self.MainPolynomial.coefficients()
        for p in self.Monomials:
            if p in fmono:
                c.append(fcoef[fmono.index(p)])
            else:
                c.append(0)
        return c
            
        
    def Calpha(self, mono, Mmnt):
        r"""
        returns $C_{\alpha,idx}$ where $\alpha$ is the exponent of mono
        """
        
        r = Mmnt.nrows()
        C = Matrix(self.Field, r, r)
        for i in range(r):
            for j in range(i,r):
                entity = Mmnt[i,j]
                entity_monos = entity.monomials()
                entity_coefs = entity.coefficients()
                if mono in entity_monos:
                    C[i,j] = entity_coefs[entity_monos.index(mono)]
                    C[j,i] = C[i,j]
        return C
        
    def LocalizedMomentMatrix(self, idx):
        """
        Returns localized moment matrix corresponding to $g_{idx}$
        """
        
        tmp_vec = self.MonomialsVec(self.Relaxation-self.HalfDegs[idx])
        m = Matrix(1, len(tmp_vec), tmp_vec)
        return self.Constraints[idx]* (m.transpose() * m)
                
    def init_sdp(self):
        """
		This method simply initializes the semidefinite program, 
		corresponding to the input data.
        """
        n = self.NumVars
        N = self.NumMonomials(n, 2*self.Relaxation)
        self.MatSize = [self.NumMonomials(n, self.Relaxation), N]
        Blck = [[] for i in range(N)]
        C = []
        
        for idx in range(self.NumberOfConstraints):
            d = self.NumMonomials(n, self.Relaxation - self.HalfDegs[idx])
            h = Matrix(self.Field, d, d, 0)
            C.append(h)
            Mmnt = self.LocalizedMomentMatrix(idx)
            
            for i in range(N):
                p = self.Monomials[i]
                A = self.Calpha(p, Mmnt)
                Blck[i].append(A)
            
        for i in range(N):
            Blck[i].append(Matrix(self.Field, 1, 1, 0))
            Blck[i].append(Matrix(self.Field, 1, 1, 0))
        
        Blck[0][self.NumberOfConstraints][0] = 1
        Blck[0][self.NumberOfConstraints+1][0] = -1
        C.append(Matrix(self.Field, 1, 1, 1))
        C.append(Matrix(self.Field, 1, 1, -1))
            
        self.Matrice = [C, self.PolyCoefFullVec(), Blck]
		
    def minimize(self):
        """
        Solves the semidefinite program coming from the set of input
        data and returns some information as outpu in 'Info'
        'Info' carries the following information:
			
            status':
                either 'Optimal' or 'Infeasible' based on the status of
                the solver.
            'Message':
                provides more detail on the final status of the solver
            'min':
                is the minimum computed for f over the set defined by
                g1>=0,..., gm>=0. It is None, if the solver fails.
            'Wall' & 'CPU':
                wall time and CPU time spent by the solver.
            'Size':
                a list which gives the dimention of sdp matrices
        """
        from SDP import SDP
        
        sos_sdp = SDP.sdp(solver = self.solver, Settings = {'detail':self.detail})
        sos_sdp.solve(self.Matrice[0], self.Matrice[1], self.Matrice[2])
        
        if sos_sdp.Info['Status'] == 'Optimal':
            self.f_min = min(sos_sdp.Info['PObj'], sos_sdp.Info['DObj'])
            self.Info = {"min":self.f_min, "Wall":sos_sdp.Info['Wall'], "CPU":sos_sdp.Info['CPU']}
            self.Info['status'] = 'Optimal'
            self.Info['Message'] = 'Feasible solution for moments of order ' + str(self.Relaxation)
        else:
            self.f_min = None
            self.Info['min'] = self.f_min
            self.Info['status'] = 'Infeasible'
            self.Info['Message'] = 'No feasible solution for moments of order ' + str(self.Relaxation) + ' were found'
        
        self.Info["Size"] = self.MatSize
        return self.f_min
    
    def decompose(self):
        """
            Gives an SOS decomposition of f if exists as a list of polynomials
            of at most half degree of f.
            This method also fills the 'Info' as 'minimize' does. In addition,
            returns Info['is sos'] which is Boolean depending on the status of 
            sdp solver.
        """
        n = self.NumVars
        N0 = self.NumMonomials(n, self.MainPolyHlfDeg)
        N1 = self.NumMonomials(n, self.MainPolyTotDeg)
        self.MatSize = [N0, N1]
        
        vec = self.MonomialsVec(self.MainPolyHlfDeg)
        m = Matrix(1, N0, vec)
        Mmnt = m.transpose() * m
        Blck = [[] for i in range(N1)]
        C = []
        
        h = Matrix(self.Field, N0, N0, 0)
        C.append(h)
        decomp = []
        
        for i in range(N1):
            p = self.Monomials[i]
            A = self.Calpha(p, Mmnt)
            Blck[i].append(A)
        
        from SDP import SDP
        sos_sdp = SDP.sdp(solver = self.solver, Settings = {'detail':self.detail})
        sos_sdp.solve(C, self.PolyCoefFullVec(), Blck)
        
        if sos_sdp.Info['Status'] == 'Optimal':
            self.Info['status'] = 'Feasible'
            GramMtx = Matrix(sos_sdp.Info['X'][0])
            try:
                self.Info['Message'] = "A SOS decomposition of the polynomial were found."
                self.Info['is sos'] = True
                H1 = GramMtx.cholesky();
                tmpM = Matrix(1, N0, vec)
                decomp = list(tmpM*H1)[0]
                self.Info['Wall'] = sos_sdp.Info['Wall']
                self.Info['CPU'] = sos_sdp.Info['CPU']
            except:
                self.Info['Message'] = "The given polynomial seems to be a sum of squares, but no SOS decomposition were extracted."
                self.Info['is sos'] = False
                self.Info['Wall'] = sos_sdp.Info['Wall']
                self.Info['CPU'] = sos_sdp.Info['CPU']
        else:
            self.Info['Message'] = "The given polynomial is not a sum of squares."
            self.Info['status'] = 'Infeasible'
            self.Info['is sos']= False
        
        self.Info["Size"] = self.MatSize
        return decomp
    
    def GradientIdealMethod(self,method = 'original'):
        """
            This method finds a lower bound for f over the 
            semilagebraic set g1>=0,..., gm>=0 intersected
            by the gradient variety of f as suggested by
            Demmel, Nie and Sturmfels.
            
            Arguments:
                method:
                    'original':
                        uses the original method 
                    'groebner':
                        computes the groebner basis of the
                        gradient ideal then applies method.
        """
        TempConstraints = self.Constraints
        TempHalfDegs = self.HalfDegs
        TempNumberOfConstraints = self.NumberOfConstraints
        f = self.MainPolynomial
        if method == 'original':
            for x in self.vars:
                g = diff(f, x)
                self.Constraints.append(g)
                self.Constraints.append(-g)
                tmp_deg = g.total_degree()
                if (tmp_deg % 2) == 1:
                    hlf_deg = (tmp_deg + 1)/2
                else:
                    hlf_deg = tmp_deg/2
                self.HalfDegs.append(hlf_deg)
                self.HalfDegs.append(hlf_deg)
                self.NumberOfConstraints += 2
        else:
            ID = self.Ring.ideal([diff(f, v) for v in self.vars])
            GB = ID.groebner_basis()
            for g in GB:
                self.Constraints.append(g)
                self.Constraints.append(-g)
                tmp_deg = g.total_degree()
                if (tmp_deg % 2) == 1:
                    hlf_deg = (tmp_deg + 1)/2
                else:
                    hlf_deg = tmp_deg/2
                self.HalfDegs.append(hlf_deg)
                self.HalfDegs.append(hlf_deg)
                self.NumberOfConstraints += 2
        
        self.init_sdp()
        self.minimize()
        
        self.Constraints = TempConstraints
        self.HalfDegs = TempHalfDegs
        self.NumberOfConstraints = TempNumberOfConstraints
