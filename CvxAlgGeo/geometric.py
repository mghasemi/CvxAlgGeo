#**********************************************************************#
#       Copyright (C) 2011-2013 Mehdi Ghasemi <mehdi.ghasemi@usask.ca> #
#                                                                      #
#  Distributed under the terms of the GNU General Public License (GPL) #
#  as published by the Free Software Foundation; either version 2 of   #
#  the License, or (at your option) any later version                  #
#                  http://www.gnu.org/licenses/                        #
#**********************************************************************#


from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.real_mpfr import *
from sage.matrix.constructor import Matrix, identity_matrix

class GPTools:
    """
    A class to find lower bounds of an even degree polynomial, using 
    Geometric Programs.
    """
    
    number_of_variables = 1
    total_degree = 2
    polynomial = 0
    constant_term = 0
    constant_terms = []
    fgp = 0
    Info = {'status':''}
    MarginalCoeffs = []
    MaxIdx = 0
    Ord = 0
    Prog = []
    
    def __init__(self, Prg, Rng, H = [], Settings = {'Iterations':150,'detail':True,'tryKKT':0, 'AutoMatrix':True, 'precision':7}):
        
        f = Prg[0]
        self.Prog = []
        self.PolyRng = Rng
        self.VARS = self.PolyRng.gens()
        self.polynomial = f
        self.Field = self.polynomial.base_ring()
        self.number_of_variables = len(self.VARS)
        self.total_degree = f.total_degree()
        self.constant_term = f.constant_coefficient()
        self.prg_size = 1
        if len(Prg) > 1:
            self.prg_size = len(Prg[1]) + 1
        if H == []:
            self.H = identity_matrix(self.Field, self.prg_size)
        else:
            self.H = H
        self.Prog.append(f)
        self.constant_terms.append(f.constant_coefficient())
        for i in range(self.prg_size - 1):
            self.Prog.append(Prg[1][i])
            self.constant_terms.append(Prg[1][i].constant_coefficient())
            tmp_deg = Prg[1][i].total_degree()
            if self.total_degree < tmp_deg:
               self.total_degree = tmp_deg
        self.Settings = Settings
        if 'AutoMatrix' in Settings:
            self.AutoMatrix = Settings['AutoMatrix']
        else:
            self.AutoMatrix = False
        if 'Order' in Settings:
            self.Ord = max(Settings['Order'], self.total_degree)
        else:
            self.Ord = self.total_degree
        if (self.Ord % 2) == 1:
            self.Ord = self.Ord + 1
            self.MarginalCoeffs = []
        if 'precision' in Settings:
            self.error_bound = 10**(-Settings['precision'])
        else:
            self.error_bound = 10**(-7)
        self.Info = {'gp':0,'CPU':0,'Wall':0,'status':'Unknown','Message':''}
            
    def is_square_mono(self, mono, coef):
        """
        This functions gets the coefficient and the exponent of a term and returns 
        True if it is an square term and False otherwise.
        """
        
        flag=True
        if coef < 0:
            return False
        exp = mono.exponents()
        for ex in exp[0]:
            flag = flag & (ex%2 == 0)
        return flag

    def UDelta(self):
        """
        This method returns a list consists of 0:coefficients, 1: monomials, 
        2: total degree of monomials, 3: number of non-zero exponents
        for those terms that are not square in the program.
        """
        
        Dlt = [[], [], [], []]    #Dlt[0]:Coefs     Dlt[1]:Monos     Dlt[2]:Degree     Delt[3]:n_alpha
        idx = 0
        diagonal_monos = [p**self.Ord for p in self.VARS]
        diagonal_monos.append(1)
        for tf in self.Prog:
            if idx == 0:
                f = tf
            else:
                f = -tf
            coefs = f.coefficients()
            monos = f.monomials()
            num_terms = len(coefs)
            for i in range(num_terms):
                if (monos[i] not in diagonal_monos) and (monos[i] not in Dlt[1]) and (not self.is_square_mono(monos[i], coefs[i])):
                    Dlt[0].append(coefs[i])
                    Dlt[1].append(monos[i])
                    Dlt[2].append(monos[i].total_degree())
                    Dlt[3].append(self.n_alpha(monos[i].exponents()[0]))
            idx += 1
        self.UDlt = Dlt
    
    def tuple_to_exp(self, t1, t2):
        """
        This function takes two tuple of real numbers, raise each one in the 
    	fist one to the power of the corresponding entity in the second and then
    	multiply them together.
        """
    
        mlt = 1
        n = len(t1)
        for i in range(0, n):
            if (t1[i] == 0) and (t2[i] == 0):
                continue
            mlt *= t1[i]**t2[i]
        return mlt
    
    def n_alpha(self, alpha):
        """
        This function, counts the number of non-zero entities in the given 
    	exponent.
        """
    
        num = 0
        for i in alpha:
            if i != 0:
                num += 1
        return num
        
    def non_zero_before(self, mon, idx):
        """
        Counts the number of auxiliary lifting variables before a variable
        in a certain monomial.
        """
        
        cnt = 0
        for i in range(idx):
            if mon[i] != 0:
                cnt += 1
        return cnt
    
    def Matrix2CVXOPT(self, M):
        """
        Converts a Sage matrix into a matrix acceptable for 
        the CvxOpt package.
        """
        
        from cvxopt.base import matrix as Mtx
        from array import array
        
        n = M.ncols()
        m = M.nrows()
        CM = []
        for j in range(n):
            for i in range(m):
                CM.append(M[i, j])
        CC = Mtx(array('d', CM), (m, n))
        return CC
    
    def auto_matrix(self):
        """
        Returns a candidate for matrix H
        """
        
        self.H = identity_matrix(self.Field, self.prg_size)
        diagonal_terms = [p**self.Ord for p in self.VARS]
        
        thm42 = True
        rmk43 = True
        
        for i in range(self.number_of_variables):
            nonzero = False
            k = self.prg_size
            while not nonzero:
                k -= 1
                if k < 0:
                    break
                gkdi = 0
                if diagonal_terms[i] in self.Prog[k].monomials():
                    gkdi = self.Prog[k].coefficients()[self.Prog[k].monomials().index(diagonal_terms[i])]
                if gkdi != 0:
                    nonzero = True
            if gkdi > 0:
                thm42 = False
                rmk43 = False
                break
            for j in range(k):
                gjdi = 0
                if diagonal_terms[i] in self.Prog[j].monomials():
                    gjdi = self.Prog[j].coefficients()[self.Prog[j].monomials().index(diagonal_terms[i])]
                if gjdi < 0:
                    rmk43 = False
                    break
        if rmk43:
            for j in range(1, self.prg_size):
                sums = [0]
                for i in range(self.number_of_variables):
                    g0di = 0
                    if diagonal_terms[i] in self.Prog[0].monomials():
                        g0di = -self.Prog[0].coefficients()[self.Prog[0].monomials().index(diagonal_terms[i])]
                    tmp = g0di
                    gjdi = 0
                    if diagonal_terms[i] in self.Prog[j].monomials():
                        gjdi = self.Prog[j].coefficients()[self.Prog[j].monomials().index(diagonal_terms[i])]
                    if gjdi != 0:
                        for jp in range(1, j):
                            gjpdi = 0
                            if diagonal_terms[i] in self.Prog[jp].monomials():
                                gjpdi = self.Prog[jp].coefficients()[self.Prog[jp].monomials().index(diagonal_terms[i])]
                            tmp += self.H[jp, 0]*gjpdi
                        sums.append(tmp/gjdi)
                self.H[j, 0] = -max(sums)
            return
        if thm42:
            for j in range(self.prg_size):
                for k in range(j):
                    sums = [0]
                    for i in range(self.number_of_variables):
                        gjdi = 0
                        if diagonal_terms[i] in self.Prog[j].monomials():
                            gjdi = self.Prog[j].coefficients()[self.Prog[j].monomials().index(diagonal_terms[i])]
                        rest_are_zero = True
                        for jp in range(j+1, self.prg_size):
                            gjpdi = 0
                            if diagonal_terms[i] in self.Prog[jp].monomials():
                                gjpdi = self.Prog[jp].coefficients()[self.Prog[jp].monomials().index(diagonal_terms[i])]
                            if gjpdi != 0:
                                rest_are_zero = False
                        if (gjdi < 0) and rest_are_zero:
                            tmp = gjdi
                            for jp in range(k+1, j):
                                gjpdi = 0
                                if diagonal_terms[i] in self.Prog[jp].monomials():
                                    gjpdi = self.Prog[jp].coefficients()[self.Prog[jp].monomials().index(diagonal_terms[i])]
                                tmp += self.H[jp, k]*gjpdi
                            sums.append(-tmp/gjdi)
                        self.H[j, k] = min(sums)
    
    def init_geometric_program(self):
	"""
	This function initializes the geometric program associated to 
	the input a polynomial.
	"""
        from math import log
        self.UDelta()
        num_z_alpha = sum(self.UDlt[3])
        num_w_alpha = len(self.UDlt[0])
        num_lambda = len(self.Prog) - 1
        big_dim = num_z_alpha + num_w_alpha + num_lambda
        zero_row = [0 for i in range(big_dim)]
        d = self.Ord
        diagonal_terms = [p**d for p in self.VARS]
        Kt = []
        Gt = []
        Ft = []
        if self.AutoMatrix:
            self.auto_matrix()
        H2 = self.H
        H2[0,0] = -self.H[0, 0]
        POLYS = Matrix(self.Prog)*H2
        self.constant_term = POLYS[0][0].constant_coefficient()
        
        ##########  Objective function: ##########
        ### sum over |alpha|<2d for objective: ###
        Ftr = [0 for l in range(big_dim)]
        var_before = 0
        term_cnt = 0
        for i in range(num_w_alpha):
            tmp_exp = self.UDlt[1][i].exponents()[0]
            absalpha = self.UDlt[2][i]
            if absalpha < d:
                Gt.append(log((d-absalpha)*(self.tuple_to_exp(tmp_exp,tmp_exp)*(1.0/d)**d)**(1.0/(d-absalpha))))
                for j in range(self.number_of_variables):
                    if tmp_exp[j] != 0:
                        Ftr[var_before] = -tmp_exp[j]*(1.0/(d-absalpha))
                        var_before += 1
                Ftr[num_z_alpha+i] = d*(1.0/(d-absalpha))
                Ft.append(Ftr)
                Ftr = [0 for l in range(big_dim)]
                term_cnt += 1
            else:
                var_before += self.UDlt[3][i]
        ### Linear part: ###
        for j in range(1, self.prg_size):
            if POLYS[0][j].constant_coefficient() > 0:
                Gt.append(log(POLYS[0][j].constant_coefficient()))
                Ftr[num_z_alpha+num_w_alpha + j - 1] = 1
                Ft.append(Ftr)
                Ftr = [0 for l in range(big_dim)]
                term_cnt += 1
        if term_cnt > 0:
            Kt.append(term_cnt)
        ### End ###
        
        ### constraint set 1 for i=1,...,n ###
        self.geometric_program = True
        for j in range(self.number_of_variables):
            Ftr = [0 for l in range(big_dim)]
            var_before = 0
            term_cnt = 0
            lmbd = []
            pos_idx = -1
            positive_term_counter = 0
            for k in range(self.prg_size):
                sgn = -1
                if diagonal_terms[j] in POLYS[0][k].monomials():
                    Glambda = sgn*POLYS[0][k].coefficients()[POLYS[0][k].monomials().index(diagonal_terms[j])]
                    if Glambda > 0:
                        pos_idx = k
                        positive_term_counter += 1
                    lmbd.append(Glambda)
                else:
                    lmbd.append(0)
            ### Check for consistency: ###
            if positive_term_counter > 1:
                self.geometric_program = False
            ### ###
            if pos_idx >= 0:
                for i in range(num_w_alpha):
                    tmp_exp = self.UDlt[1][i].exponents()[0]
                    if (tmp_exp[j] != 0):
                        ### ###
                        Gt.append(-log(lmbd[pos_idx]))
                        Ftr[var_before + self.non_zero_before(tmp_exp, j)] = 1
                        if pos_idx > 0:
                            Ftr[num_z_alpha+num_w_alpha+pos_idx - 1] = -1
                        Ft.append(Ftr)
                        Ftr = [0 for l in range(big_dim)]
                        term_cnt += 1
                    var_before += self.UDlt[3][i]
                for k in range(self.prg_size):
                    if (k != pos_idx) and (lmbd[k] != 0):
                        Gt.append(log(-lmbd[k]) - log(lmbd[pos_idx]))
                        if k > 0:
                            Ftr[num_z_alpha + num_w_alpha + k - 1] = 1
                        if pos_idx > 0:
                            Ftr[num_z_alpha + num_w_alpha + pos_idx - 1] = -1
                        Ft.append(Ftr)
                        Ftr = [0 for l in range(big_dim)]
                        term_cnt += 1
                if term_cnt > 0:
                    Kt.append(term_cnt)
        ### End ###
        
        ### Constraints for |alpha|=2d: ###
        var_before = 0
        for i in range(num_w_alpha):
            if self.UDlt[2][i] == d:
                tmp_exp = self.UDlt[1][i].exponents()[0]
                Gt.append(log(self.tuple_to_exp(tmp_exp,tmp_exp)*(1.0/d)**d))
                Ftr[num_z_alpha + i] = d
                for j in range(self.number_of_variables):
                    if tmp_exp[j] != 0:
                        Ftr[var_before + j] = -tmp_exp[j]
                Ft.append(Ftr)
                Ftr=[0 for l in range(big_dim)]
                Kt.append(1)
            var_before += self.UDlt[3][i]
        ### End ###
        
        ### Constraints for H^+ & H^-: ###
        for i in range(num_w_alpha):
            Gp = []
            Gm = []
            sgn = 1
            for k in range(self.prg_size):
                if k > 0:
                    sgn = 1
                Glambda = 0
                if self.UDlt[1][i] in POLYS[0][k].monomials():
                    Glambda = sgn*POLYS[0][k].coefficients()[POLYS[0][k].monomials().index(self.UDlt[1][i])]
                if Glambda >= 0:
                    Gm.append(Glambda)
                    Gp.append(0)
                else:
                    Gp.append(-Glambda)
                    Gm.append(0)
            term_cnt = 0
            for k in range(self.prg_size):
                if Gm[k] > 0:
                    Gt.append(log(Gm[k]))
                    if k > 0:
                        Ftr[num_z_alpha + num_w_alpha + k - 1] = 1
                    Ftr[num_z_alpha + i] = -1
                    term_cnt += 1
                    Ft.append(Ftr)
                    Ftr = [0 for l in range(big_dim)]
            if term_cnt > 0:
                Kt.append(term_cnt)
            term_cnt = 0
            for k in range(self.prg_size):
                if Gp[k] > 0:
                    Gt.append(log(Gp[k]))
                    if k > 0:
                        Ftr[num_z_alpha + num_w_alpha + k - 1] = 1
                    Ftr[num_z_alpha + i] = -1
                    term_cnt += 1
                    Ft.append(Ftr)
                    Ftr = [0 for l in range(big_dim)]
            if term_cnt > 0:
                Kt.append(term_cnt)
        ### Constraints for rows of H: ###
        for j in range(self.prg_size):
            num_nzr = 0
            num_pos = 0
            pos_idx = 0
            term_cnt= 0
            idx = 0
            for a in self.H[j]:
                if a != 0:
                    num_nzr += 1
                if a > 0:
                    num_pos += 1
                    pos_idx = idx
                idx += 1
            if (num_pos > 1) and (num_pos != num_nzr):
                self.geometric_program = False
            elif (num_pos != num_nzr) and (num_pos == 1):
                for k in range(self.prg_size):
                    if (k != pos_idx) and (self.H[j, k] != 0):
                        Gt.append(log(-self.H[j, k]/self.H[j, pos_idx]))
                        if k > 0:
                            Ftr[num_z_alpha + num_w_alpha + k - 1] = 1
                        if pos_idx > 0:
                            Ftr[num_z_alpha + num_w_alpha +pos_idx - 1] = -1
                        term_cnt += 1
                        Ft.append(Ftr)
                        Ftr = [0 for l in range(big_dim)]
                if term_cnt > 0:
                    Kt.append(term_cnt)
        return [Matrix(Gt).transpose(), Matrix(Ft), Kt]
    
    def minimize(self):
        """
        The main function to compute the lower bound for an
        even degree polynomial, using Geometric Program.
        """
        
        from cvxopt import solvers
        from time import time, clock
        from math import exp
        RealNumber = float  # Required for CvxOpt
        Integer = int       # Required for CvxOpt
        
        if 'Iterations' in self.Settings:
            solvers.options['maxiters'] = self.Settings['Iterations']
        else:
            solvers.options['maxiters'] = 100
        if 'Details' in self.Settings:
            solvers.options['show_progress'] = self.Settings['detail']
        else:
            solvers.options['show_progress'] = False
        if 'tryKKT' in self.Settings:
            solvers.options['refinement'] = self.Settings['tryKKT']
        else:
            solvers.options['refinement'] = 1
        
        n = self.number_of_variables
        d = self.Ord
        f = self.polynomial
        GP = self.init_geometric_program()
        f0 = self.constant_term
        if not self.geometric_program:
            self.Info['status'] = 'Inapplicable'
            self.Info['Message'] = 'The input data does not result in a geometric program'
            self.Info['gp'] = None
            self.fgp = None
            return self.fgp
        F = self.Matrix2CVXOPT(GP[1])
        g = self.Matrix2CVXOPT(GP[0])
        K = GP[2]
        start = time()
        start2 = clock()
        #if True:
        try:
            sol = solvers.gp(K=K, F=F, g=g)
            elapsed = (time() - start)
            elapsed2 = (clock()-start2)
            self.fgp = min(-f0-exp(sol['primal objective']), -f0-exp(sol['dual objective']))
            self.Info = {"gp":self.fgp, "Wall":elapsed, "CPU":elapsed2}
            if (sol['status'] == 'unknown'):
                if (abs(sol['relative gap']) < self.error_bound) or (abs(sol['gap']) < self.error_bound):
                    self.Info['status'] = 'The solver did not converge to a solution'
                    self.Info['Message'] = 'A possible optimum value were found.'
                else:
                    self.Info['status'] = 'Singular KKT or non-convergent IP may occurd'
                    self.Info['Message'] = 'Maximum iteration has reached by solver or a singular KKT matrix occurred.'
            else:
                self.Info['status'] = 'Optimal'
                self.Info['Message'] = 'Optimal solution found by solver.'
        except:
            self.Info['Message'] = "An error has occurred on CvxOpt.GP solver."
            self.Info['status'] = 'Infeasible'
            self.Info['gp'] = None
            self.fgp = None
        return self.fgp

########################################################################
