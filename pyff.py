#version 0.2

import copy
import numpy as np
from math import sqrt,factorial,floor
import itertools

#----------------------------------------------#
#
# class FF
#
#----------------------------------------------#
          
class FF:
    """ Class to construct a finite field, it contains
        (1) is_prime: to test the characteristic
        (2) minimum_polynomial: to generated a minimum polynomial for each generated finite field
        (3) minimum_polynomial_in_X: for a ``human" display of the minimum polynomial
        (4) elt: to create an element within the finite field
        (5) add: to sum two finite field elements
        (6) subtract: to subtract a finite field element from another
        (7) mult: to multiply two finite field elements
        (8) gcd_euclid: the extended Euclidean algorithm that find the gcd and solves Bezout
        (9) inverse_modp: to invert mod p
        (10) randelt: to create a random element of the finite field
        (11) randpoly: to generate a random polynomial of given degree
        (12) change_minimum_polynomial: to use a different minimum polynomial
        (13) exp: modular exponentiation
        (14) display_in: to display elements of F_q using a generator (choice of notation for the generator)
        (15) identity_matrix: to generate an identity matrix of chosen size
        (16) ones_matrix: to generate a matrix containing only ones of chosen size
        (17) zeros_matrix: to generate a matrix containing only zeroes of chosen size
        (18) rand_matrix: to generate a matrix of chosen size containing random field elements 
        (19) primitive_elt: to compute a primitive element
    """
    def is_prime(self,input_int):
        """ Primality test using Eratostenes Sieve, which is very inefficient.
            However it should be enough to handle the characteristic of the field of interest.
        """
        assert type(input_int) == int, "The input should be an integer."
        input_is_prime = True
        #creates a list of integers from 2 to sqrt{input_int}
        lst_integers = range(2,int(sqrt(input_int))+1)
        #starts with p = 2
        primes = [2]
        cnt = -1
        while len(lst_integers)>0 and input_is_prime == True:
                cnt = cnt+1
                #tests if current prime divides the input
                if input_int%primes[cnt] == 0:
                    input_is_prime = False
                #finds all multiples of p
                lst_sieved = [x for x in range(1,int(sqrt(input_int))+1) if x%primes[cnt] == 0] 
                #removes the multiples from the list of integers
                lst_integers = [x for x in lst_integers if not(x in lst_sieved)]
                if len(lst_integers)>0:
                    #keeps the smallest integer of the expunged list which is a prime
                    primes.append(min(lst_integers))
        return input_is_prime
        
        
    def factor(self,n):
        """This is the naive trial division, code taking from wikipedia.
           It is very inefficient, but it is used as input to Rabin test, 
           to factor the degree of the polynomial. 
        """
        assert type(n) == int, "The input should be an integer."
        a = []
        while n % 2 == 0:
            a.append(2)
            n /= 2
        f = 3
        while f * f <= n:
            if n % f == 0:
                a.append(f)
                n /= f
            else:
                f += 2
        if n != 1: a.append(n)
        # returns a list of prime factors, if p^2 appears, p is repeated
        return [int(x) for x in a]

    
    def minimum_polynomial(self):
        """Computes a minimal polynomial for the field extension.
           If the dimension 1, returns the constant polynomial 1.
        """
        if self.char == self.size:
            output = FFPoly(self,[1]) 
        else:
            mu = self.ground_field.randpoly(self.dim)
            while mu.is_irreducible() == False:
                mu = self.ground_field.randpoly(self.dim)
            #makes the polynomials monic
            if not(mu.coefficients[0] == 1):
                mu0inv = mu.coeffs_field.inverse_modp(mu.coefficients[0])
                output = mu.mult_by_scalar(mu0inv)
            else:
                output = mu
        return output
    
    
    def minimum_polynomial_in_X(self):
        """It takes the coefficients of the minimum polynomial, 
           and writes them in the form of a polynomial in X.
           This representation is not usable for computation.
        """
        return self.minimum_polynomial.display_in_X()
        
    
    def __init__(self,base,exponent):
        """ A finite field is specified by its size q = p^r, p is the base or characteristics, 
            r is the exponent or dimension, e.g. F5 = FF(5,1), F25 = FF(5,2). 
            The base is necessarily a prime number, and the exponent necessarily a positive nonzero integer.
            When created, a finite field comes with
            (1) its characteristic FF.char
            (2) its dimension FF.dim
            (3) its size FF.size
            (4) a ground field FF.ground_field
            (5) a generator w such that F_q = F_p[w] given in the basis (1,w,..,w^{r-1})
        """
        assert type(base) == int and base > 1, "base (or characteristic) should be an integer at least 2"
        assert self.is_prime(base), "base (or characteristic) should be prime"
        assert type(exponent) == int and exponent > 0, "exponent should be an integer at least 1"
        
        self.char = base
        self.dim = exponent
        self.size = base**exponent
        if self.dim > 1:
            self.ground_field = FF(self.char,1)
        self.variable = 'w'
        if self.dim == 1:
            self.zero = 0
            self.one = 1
        else:
            self.zero = [0 for cnt in range(self.dim)]
            self.one = [1] + [0 for cnt in range(self.dim-1)]
        self.generator = [self.zero if not(idx==1) else self.one for idx in range(self.dim)] 
        self.minimum_polynomial = self.minimum_polynomial()

        
    def elt(self,lst_coeffs):
        """ A finite field element exists only with respect to a finite field. 
            It is defined by either an integer (in which case this integer modulo p is understood), 
            or a list of integers of length r = exponent, in which case the element is understood as 
            a vector over F_p, for p = base (or characteristics), and the integers in the list are 
            also understoold modulo p. The ith list coefficient corresponds to the coefficient of w^i, 
            for w a generator of F_{p^r} using the isormorphism F_p[w] with F_p-basis {1,w,...,w^(r-1)} 
            e.g. F5.Elt(4), F25.Elt([0,1]).
            A generator w is computed by default once the finite field is created.
        """
        condition1 = (type(lst_coeffs) == list and all([type(x)==int for x in lst_coeffs]))
        condition2 = (type(lst_coeffs) == int)
        
        assert condition1 or condition2, "lst_coeffs should be either one integer or a list of integers"
        assert condition2 or (condition1 and len(lst_coeffs) == self.dim), "the list should be of length the dimension over F_p"
        assert condition1 or (condition2 and self.dim == 1), "the list should be of length the dimension over F_p"
        
        if condition1: 
            if len(lst_coeffs) == 1:
                output = lst_coeffs[0]%self.char
            else:
                output = [x%self.char for x in lst_coeffs]
        else:
            output = lst_coeffs%self.char
        
        return output
        
        
    def add(self,a,b):
        """ Sums two elements in a finite field. The function calls self.elt which does the 
            check on the formatting of the inputs. 
            Possible inputs: a single integer for F_p, or a list of integers for F_{p^r}.
        """
        if self.char == self.size:
            a_plus_b = (self.elt(a)+self.elt(b))%self.char
        else:
            a_plus_b = [self.ground_field.add(self.elt(a)[i],self.elt(b)[i]) for i in range(self.dim)]
        
        return a_plus_b 
    
    def subtract(self,a,b):
        """ Subtract an element b from an element a both in a finite field. The function calls self.elt which does the 
            check on the formatting of the inputs. 
            Possible inputs: a single integer for F_p, or a list of integers for F_{p^r}.
        """
        if self.char == self.size:
            a_plus_b = (self.elt(a)-self.elt(b))%self.char
        else:
            a_plus_b = [ (self.elt(a)[i]-self.elt(b)[i])%self.char for i in range(self.dim)]
        
        return a_plus_b 
    
    def mult(self,a,b):
        """ Multiplies two elements in a finite field. The function calls self.elt which does the 
            check on the formatting of the inputs. 
            Possible inputs: a single integer for F_p, or a list of integers for F_{p^r}. 
        """
        if self.char == self.size:
            a_times_b = (self.elt(a)*self.elt(b))%self.char
        else:
            a = self.elt(a)
            b = self.elt(b)
            a_times_b = [self.ground_field.mult(b[0],x) for x in a]
            #coefficients of the minimal polynomial 
            mu_poly = self.minimum_polynomial.coefficients[::-1]
            for i in range(1,self.dim):
                terms = [self.ground_field.zero for cnt in range(i)]+[self.ground_field.mult(b[i],x) for x in a[:-i]]
                ab = self.ground_field.mult(a[i],b[i])
                dom_term = [self.ground_field.mult(ab,self.ground_field.subtract(self.ground_field.zero,x)) for x in mu_poly[:-1]]
                all_terms = [self.ground_field.add(terms[j],dom_term[j]) for j in range(self.dim)]
                a_times_b = [self.ground_field.add(all_terms[j],a_times_b[j]) for j in range(self.dim)]
        return a_times_b
    
    
    def gcd_euclid(self,a,b):
        """ Extended Euclidean algorithm to compute the gcd of two integers.
            Code taken from https://brilliant.org/wiki/extended-euclidean-algorithm/
            returns gcd, x, y such that gcd = ax+by
        """
        assert type(a) == int and type(b) == int, "The input should be integers."
        x,y,u,v = 0,1,1,0
        while a != 0:
            q, r = b//a, b%a
            m, n = x-u*q, y-v*q
            b,a, x,y, u,v = a,r, u,v, m,n
        gcd = b
        return [self.elt(gcd),self.elt(x),self.elt(y)]
    
    
    def inverse_modp(self,a):
        """ Given an element a in a finite field, computes its multiplicative inverse.
            The function calls self.elt which does the check on the formatting of the inputs. 
        """
        a = self.elt(a)
        if self.char == self.size:
            assert not(a%self.char==0), '0 is not invertible'
            res = self.gcd_euclid(a,self.char)
            output = res[1]
        else: 
            assert not(a == self.zero),'0 is not invertible'
            res = FFPoly(self.ground_field,a[::-1]).gcd_euclid(self.minimum_polynomial)
            respoly = (res[1]).coefficients[::-1]
            output = respoly + [0 for cnt in range(self.dim-len(respoly))]
        return output
    
    
    def randelt(self):
        """ Generates a random element.
        """
        if self.char == self.size:
            elt = np.random.randint(self.char)
        else:
            elt = [self.ground_field.randelt() for r in range(self.dim)]
        return elt
    
    
    def randpoly(self,n):
        """Generate a random polynomial of degree n over the ground field.
           The result is a new polynomial, an instance of FFPoly.
        """
        assert type(n) == int, "The input should be an integer."
        #makes sure the leading coefficient is not zero
        if self.dim == 1:
            lc = 0
            while lc==0:
                lc = self.randelt()
        else:
            lc = self.zero
            while lc==self.zero:
                lc = self.randelt()   
            
        return FFPoly(self,[lc]+[self.randelt() for cnt in range(n)])
     
        
    def change_minimum_polynomial(self,p):
        """Changes the minimum polynomial, based on user input.
           Checks whether the polynomial is indeed irreducible.
        """
        assert self.dim > 1, "Available for q^r, r>1"
        assert p.is_irreducible(), "Choose an irreducible polynomial"
        self.minimum_polynomial = p
        
    
    def exp(self,a,n):
        """ Given an finite field element a, computes a^n.
        """
        assert type(n) == int, "The exponent should be an integer."
        #this checks the format of the input
        a = self.elt(a)
        if self.dim == 1:
            an = 1
            for i in range(n):
                an = (an*a)%self.char
        else: 
            an = self.one
            for i in range(n):
                an = self.mult(an,a)
        return an
    
    
    def display_in(self,a):
        """It takes the coefficients of the finite field element a in an F_p-basis, 
           and writes them in the form of a polynomial in var (var is a notation for the generator).
           var is defined to be 'w', it can be changed using the method change_variable
           This representation is not usable for computation.
        """
        var = self.variable
        a = self.elt(a)
        if self.dim > 1:
            a = a[::-1]
            elt_str = ""
            for i in range(self.dim):
                if a[i] == 1:
                    if i == self.dim-1:
                        elt_str = '1' + elt_str 
                    elif i == self.dim-2:
                        elt_str = '+' + var + elt_str 
                    else:
                        elt_str = '+' + var +'^%d'%(self.dim-i-1) + elt_str
                else:
                    if not(a[i] == 0):
                        if i == self.dim-1:
                            elt_str =  str(a[i]) + elt_str 
                        elif i == self.dim-2:
                            elt_str = '+' + str(a[i]) + var + elt_str 
                        else: 
                            elt_str = '+' + var  +'^%d'%(self.dim-i-1) + str(a[i]) +  elt_str
                    else: 
                        if i == self.dim-1:
                            elt_str = elt_str[1:] 
            if all([x==0 for x in a]):
                elt_str = '0'
        else: 
            elt_str = str(a)
        return elt_str
    
    def change_variable(self,var):
        """Changes the variable in which to display the generator of the finite field.
        """
        assert self.dim > 1, "Available for q^r, r>1"
        assert type(var) == str, "Choose a variable name (a string)"
        self.variable = var
    
    
    def identity_matrix(self,n):
        """Creates an identity matrix of size m over the given finite field
        """
        assert type(n) == int, "The input should be an integer."
        rows = []
        for r in range(n): 
            row_tmp = [self.zero for cnt in range(n)]
            row_tmp[r] = self.one
            rows.append(row_tmp)
        return FFMat(self,rows)
    
    
    def zeros_matrix(self,m,n):
        """Creates a whole zero matrix of size mxn over the given finite field
        """
        assert type(m) == int and type(n) == int, "The input should be two integers."
        rows = []
        for r in range(m): 
            rows.append([self.zero for cnt in range(n)])
        return FFMat(self,rows)
    
    
    def ones_matrix(self,m,n):
        """Creates a whole one matrix of size mxn over the given finite field
        """
        assert type(m) == int and type(n) == int, "The input should be two integers."
        rows = []
        for r in range(m): 
            rows.append([self.one for cnt in range(n)])
        return FFMat(self,rows)

    
    def rand_matrix(self,m,n):
        """Creates a random matrix of size mxn over the given finite field
        """
        assert type(m) == int and type(n) == int, "The input should be two integers."
        rows = []
        for r in range(m): 
            rows.append([self.randelt() for cnt in range(n)])
        return FFMat(self,rows)

    
    def primitive_elt(self):
        """Computes a primitive element of the given finite field
        """
        primelt = 0
        if self.char == self.size:
            while primelt == 0:
                test = self.randelt()
                if len(set([self.exp(test,i) for i in range(self.size-1)])) == self.size-1:
                    primelt = test
        else: 
            while primelt == 0:
                test = self.randelt()
                testgen = [self.exp(test,i) for i in range(self.size-1)]
                #cannot go from list of sublists to set 
                if len([list(i) for i in set(map(tuple, testgen))]) == self.size-1:
                    primelt = test
        return primelt


#----------------------------------------------------------#
#
# class FFPoly
#
#----------------------------------------------------------#

class FFPoly:
    """ Class to construct a polynomial over a finite field, it contains:
        (1) display_in_X: for a "human" display of polynomials
        (2) evaluation: to evaluate a polynomial in a finite field element
        (3) add: to add a polynomial to a given one
        (4) mult: to multiply a polynomial with a given one
        (5) divided_by: to divide a polyomial with a given one and return quotient and remainder
        (6) gcd_euclid: to compute the gcd of a polynomial with a given one, also return Bezout coefficients
        (7) is_irreducible: to check if a polynomial is irreducible
        (8) mult_by_scalar: to multiply a polynomial with a scalar from ground field
        (9) subtract: to subtract a polynomial from another one
    """ 
    def __init__(self, finite_field, poly_coeffs):
        """ Takes the ground finite field and a list as inputs, 
            the list contains the coefficients of the polynomial,  
            it is assumed the list is of the form [p_n,...,p_1,p_0].
            If the ground field is F_{p^r} with r at least 2, then each p_i is 
            a list of integers of length r.
            If p_n = 0, no error is given, a shorter list with nonzero leading coefficient 
            is created instead.
        """
        #defines whether the coefficients live
        self.coeffs_field = finite_field
        
        assert type(poly_coeffs) == list, "poly_coeffs should be a list" 
        
        #defines the degree and the coefficients
        #checks whether the coefficients are well defined by invoking elt
        #zero polynomial is treated separately
        if all([self.coeffs_field.elt(x) == self.coeffs_field.zero for x in poly_coeffs]):
                self.coefficients = [self.coeffs_field.zero]
                self.deg = 0
        else: 
            i = 0
            while self.coeffs_field.elt(poly_coeffs[i]) == self.coeffs_field.zero:
                i+=1
            self.coefficients = [self.coeffs_field.elt(x) for x in poly_coeffs[i:]]
            self.deg = len(poly_coeffs[i:])-1
                
        
    def display_in_X(self):
        """It takes the coefficients of the polynomial, 
           and writes them in the form of a polynomial in X.
           This representation is not usable for computation.
        """
        poly_str = ""
        for i in range(self.deg+1):
            if self.coefficients[i] == self.coeffs_field.one:
                if i == self.deg:
                    poly_str = poly_str + '1'
                elif i == self.deg-1:
                    poly_str = poly_str + 'X+'
                else:
                    poly_str = poly_str + 'X^%d+'%(self.deg-i) 
            else:
                if not(self.coefficients[i] == self.coeffs_field.zero):
                    if self.coeffs_field.dim > 1 :
                        nnz = len([x for x in self.coefficients[i] if not(x==0)])
                    else: 
                        nnz = 1
                    if i == self.deg:
                        if nnz > 1:
                            poly_str =  poly_str + '('+ self.coeffs_field.display_in(self.coefficients[i])+')'  
                        else:
                            poly_str =  poly_str + self.coeffs_field.display_in(self.coefficients[i])  
                    elif i == self.deg-1:
                        if nnz > 1:
                            poly_str = poly_str + '('+ self.coeffs_field.display_in(self.coefficients[i]) +')X+'
                        else: 
                            poly_str = poly_str + self.coeffs_field.display_in(self.coefficients[i]) +'X+'
                    else: 
                        if nnz > 1:
                            poly_str = poly_str + '('+ self.coeffs_field.display_in(self.coefficients[i]) +')X^%d+'%(self.deg-i)
                        else :
                            poly_str = poly_str + self.coeffs_field.display_in(self.coefficients[i]) +'X^%d+'%(self.deg-i) 
                else: 
                    if i == self.deg:
                        poly_str = poly_str[:-1] 
                    
        return poly_str
    
    
    def evaluation(self,a):
        """Evaluates the polynomial in one finite field element a.
           Calling elt checks the format of the input.
        """
        a = self.coeffs_field.elt(a)
        tmp = [self.coeffs_field.mult(self.coefficients[i],self.coeffs_field.exp(a,self.deg-i)) for i in range(self.deg+1)]
        polyeval = tmp[0]
        for i in range(1,len(tmp)):
            polyeval = self.coeffs_field.add(polyeval,tmp[i])
        return polyeval
    
    
    def add(self,q):
        """Add to a polynomial another polynomial with the same ground field.
           The result is a new polynomial, an instance of FFPoly,  
           which contains the sum of two polynomials.
        """
        assert isinstance(q,FFPoly),"The input should be an instance of FFPoly."
        if self.deg > q.deg:
            padded_p = self.coefficients
            padded_q = [self.coeffs_field.zero for cnt in range(self.deg-q.deg)] + q.coefficients
        elif self.deg < q.deg:
            padded_p = [self.coeffs_field.zero for cnt in range(q.deg-self.deg)] + self.coefficients
            padded_q = q.coefficients
        else:
            padded_p = self.coefficients
            padded_q = q.coefficients
        
        D = max(self.deg,q.deg)
        tmp = [self.coeffs_field.add(padded_p[i],padded_q[i]) for i in range(D+1)]
        return FFPoly(self.coeffs_field,tmp)
        
        
    def mult(self,q):
        """Multiply a polynomial with another polynomial with the same ground field.
           The result is a new polynomial, an instance of FFPoly,  
           which contains the product of two polynomials.
        """
        assert isinstance(q,FFPoly),"The input is an instance of FFPoly."
        prod = [self.coeffs_field.zero for cnt in range(self.deg+q.deg+1)]
        for i in range(self.deg+1):
            tmp = [self.coeffs_field.mult(self.coefficients[i],x) for x in q.coefficients]
            for j in range(len(tmp)):
                prod[i+j] = self.coeffs_field.add(prod[i+j],tmp[j])
        return FFPoly(self.coeffs_field,prod)
    
    
    def divided_by(self,b):
        """Divides a polynomial a by the polynomial b,
           outputs the quotient q and the remainder r, such that
           a = b*q + r.
           The output is two FFPoly polynomials
        """
        assert isinstance(b,FFPoly),"The input is an instance of FFPoly."
        assert (b.deg >=0) or (b.deg == 0 and not(b.coefficients[0]==self.coeffs_field.zero)), "division by zero"   
        
        q = FFPoly(self.coeffs_field,[self.coeffs_field.zero])
        r = self
        lcb_inv = self.coeffs_field.inverse_modp(b.coefficients[0])
        while not(r.coefficients == [self.coeffs_field.zero]) and r.deg >= b.deg:    
            s_coeff = self.coeffs_field.mult(r.coefficients[0],lcb_inv)
            s = FFPoly(self.coeffs_field,[s_coeff]+[self.coeffs_field.zero for cnt in range(r.deg-b.deg)])
            q = q.add(s)
            r = r.subtract(b.mult(s))
        return (q, r) 
        
        
    def gcd_euclid(self,g):
        """ Extended Euclidean algorithm to compute the gcd of two polynomial.
            returns gcd, a, b such that gcd = af+bg.
            If polynomials are not monic, the algorithm computes the gcd on the polynomials 
            obtained by factoring out the leading coefficient so the polynomials are monic. 
            This is because the gcd is defined up to unit.
            If both inputs are 0, this raises an error. If only one input is 0, then other is returned.
        """
        assert isinstance(g,FFPoly),"The input should be an instance of FFPoly."
        
        condition1 = (self.deg > 0 or (self.deg == 0 and not(self.coefficients[0]==self.coeffs_field.zero)))
        condition2 = (g.deg > 0 or (g.deg == 0 and not(g.coefficients[0]==self.coeffs_field.zero)))
        assert condition1 or condition2, "gcd(0,0) is not defined"
         
        #the constant polynomial 1
        poly1 = FFPoly(self.coeffs_field,[self.coeffs_field.one])
        #if only one input is 0 and not the other, the other is returned.
        if not(condition1) and condition2:
            return g,self,poly1
        if not(condition2) and condition1:
            return self,poly1,g
        
        #makes the polynomials monic
        if not(self.coefficients[0] == self.coeffs_field.one):
            f0inv = self.coeffs_field.inverse_modp(self.coefficients[0])
            f = self.mult_by_scalar(f0inv)
        else:
            f0inv = self.coeffs_field.one
            f = self  
        if not(g.coefficients[0] == self.coeffs_field.one):
            g0inv = self.coeffs_field.inverse_modp(g.coefficients[0])
            g = g.mult_by_scalar(g0inv)   
        else:
            g0inv = self.coeffs_field.one
        
        #the constant polynomial 0
        poly0 = FFPoly(self.coeffs_field,[self.coeffs_field.zero])
        #r,s,t,q contain polynomials
        r = [f,g]
        s = [poly1,poly0]  
        t = [poly0,poly1]
        q = [self.coeffs_field.zero]   
            
        i = 1
        while r[i].coefficients != [self.coeffs_field.zero]:
            resq,resr = r[i-1].divided_by(r[i])
            q.append(resq)
            r.append(r[i-1].subtract(q[i].mult(r[i])))
            s.append(s[i-1].subtract(q[i].mult(s[i])))
            t.append(t[i-1].subtract(q[i].mult(t[i])))   
            i+=1
        #checks if gcd polynomial is monic
        lc = r[i-1].coefficients[0]
        if lc != self.coeffs_field.one:
            lcinv = self.coeffs_field.inverse_modp(lc)
            r[i-1] = r[i-1].mult_by_scalar(lcinv)
            s[i-1] = s[i-1].mult_by_scalar(lcinv)
            t[i-1] = t[i-1].mult_by_scalar(lcinv)
        return r[i-1],s[i-1].mult_by_scalar(f0inv),t[i-1].mult_by_scalar(g0inv)
    
    
    def is_irreducible(self):
        """Checks whether a polynomial of degree n is irreducible, using Rabin's test.
           Rabin's test takes as input a monic polynomial and the factorization of n.
        """
        #makes the polynomials monic
        if not(self.coefficients[0] == self.coeffs_field.one):
            f0inv = self.coeffs_field.inverse_modp(self.coefficients[0])
            f = self.mult_by_scalar(f0inv)
        else:
            f0inv = self.coeffs_field.one
            f = self
        #factor the degree
        list_pi = list(set(self.coeffs_field.factor(self.deg)))
        k = len(list_pi)
        is_irreducible_poly = True
        n = [int(self.deg/p) for p in list_pi]
        q = self.coeffs_field.size
        for i in range(k):
            degh = q**n[i]
            minusone = self.coeffs_field.subtract(self.coeffs_field.zero,self.coeffs_field.one)
            coeffsh = [self.coeffs_field.one]+[self.coeffs_field.zero for cnt in range(degh-2)]+[minusone,self.coeffs_field.zero]
            h = FFPoly(self.coeffs_field,coeffsh)
            resq,resr = h.divided_by(f)
            hmodf = resr
            g,a,b = f.gcd_euclid(hmodf)
            if not(g.deg == 0):
                is_irreducible_poly = False
                found_factor = g
        degg = q**self.deg
        coeffsg = [self.coeffs_field.one]+[self.coeffs_field.zero for cnt in range(degh-2)]+[minusone,self.coeffs_field.zero]
        g = FFPoly(self.coeffs_field,coeffsg)
        resq,resr = g.divided_by(f)
        gmodf = resr
        if gmodf.deg == 0 and gmodf.coefficients[0] == self.coeffs_field.zero:
            is_irreducible_poly = False
        return is_irreducible_poly
    
    
    def mult_by_scalar(self,a):
        """Multiply a polynomial by a constant.
           The result is a new polynomial, an instance of FFPoly,  
           which contains the product of a polynomial with the constant.
           The call to elt checks the format of the input
        """
        a = self.coeffs_field.elt(a)
        tmp = [self.coeffs_field.mult(a,x) for x in self.coefficients]
        return FFPoly(self.coeffs_field,tmp)
        
        
    def subtract(self,q):
        """Subtract a polynomial to another polynomial with the same ground field.
           The result is a new polynomial, an instance of FFPoly,  
           which contains the difference of two polynomials.
        """
        assert isinstance(q,FFPoly),"The input is an instance of FFPoly."
        minusone = self.coeffs_field.subtract(self.coeffs_field.zero,self.coeffs_field.one)
        return self.add(q.mult_by_scalar(minusone))
    
    
    
#----------------------------------------------------------#
#
# class FFMat
#
#----------------------------------------------------------#

class FFMat:
    """ Class to construct matrices over a finite field.
        It contains:    
        (1) display: to give a nice display in Jupyter
        (2) add: to add two matrices over the same finite field
        (3) transpose: to transpose a matrix
        (4) mult: given a matrix, to multiply it wity another matrix
        (5) mult_by_scalar: to multiplity a matrix with a scalar
        (6) exp: to compute powers of a matrix
        (7) gaussian_elimination: to return an upper triangular matrix form of the matrix
        (8) det: computes the determinant
        (9) inverse_modp: computes the inverse
    """
    
    def isnotebook(self):
        """ Detects which environment is used. This is useful for the display functions.
        """
        try:
            shell = get_ipython().__class__.__name__
            if shell == 'ZMQInteractiveShell':
                return True   # Jupyter notebook or qtconsole
            elif shell == 'TerminalInteractiveShell':
                return False  # Terminal running IPython
            else:
                return False  # Other type (?)
        except NameError:
            return False      # Probably standard Python interpreter


    def __init__(self, finite_field, mat_coeffs):
        """ Takes the ground finite field and a list as inputs, 
            the list contains the coefficients of the matrix,  
            it is assumed to be a list of lists, containg the rows of the matrix.
            To create an n x m matrix, we need n lists of size m
        """
 
        #defines whether the coefficients live
        self.coeffs_field = finite_field
        
        condition1 = (type(mat_coeffs) == list and all(len(row) == len(mat_coeffs[0]) for row in mat_coeffs))
        assert condition1, "A matrix is described by a list of lists of equal size."
        
        self.dim_row = len(mat_coeffs)
        self.dim_col = len(mat_coeffs[0])
        self.dim = [self.dim_row,self.dim_col]
        #coefficients should be finite field elements
        mat_coeffs_ffelts = []
        for row in mat_coeffs:
            #this makes sure every entry is a finite field element (from the right finite field)
            mat_coeffs_ffelts.append([self.coeffs_field.elt(a) for a in row])
        self.coeffs = mat_coeffs_ffelts
       
   
    def display(self):
        """Provides a nice looking display of matrices as an html table, assuming 
           a notebook is being used.
        """
        coeffs_in = []
        for row in self.coeffs:
            coeffs_in.append([self.coeffs_field.display_in(x) for x in row])
        
        if self.isnotebook():
            from IPython.display import display, HTML 
            display(HTML('<table><tr>{}</tr></table>'.format(
           '</tr><tr>'.join(
            '<td>{}</td>'.format('</td><td>'.join(str(_) for _ in row)) for row in coeffs_in)
            )))
        else:
            print(np.array(self.coeffs))
    
    def add(self,B):
        """ Adds two matrices with coefficients in a finite field. 
            It returns an instance of FFMat.
        """
        assert (self.dim_row == B.dim_row) and (self.dim_col == B.dim_col), "Matrices need to have the same dimensions"
        A_plus_B = []
        for row in range(0,self.dim_row):
            A_plus_B.append([self.coeffs_field.add(self.coeffs[row][x],B.coeffs[row][x]) for x in range(0,self.dim_col)])
        return FFMat(self.coeffs_field,A_plus_B)
    
    def transpose(self):
        """ Transposes a matrix with coefficients in a finite field. 
        """
        return FFMat(self.coeffs_field,np.transpose(np.array(self.coeffs)).astype(np.int32).tolist())
    
    def mult(self,B):
        """ Multiplies two matrices with coefficients in a finite field. 
            It returns an instance of FFMat.
        """
        assert (self.dim_col == B.dim_row), "Matrices need to have compatible dimensions"
        A_times_B = []
        for row in range(self.dim_row):
            row_tmp = []
            for col in range(B.dim_col):
                rowcol = [self.coeffs_field.mult(self.coeffs[row][x],B.coeffs[x][col]) for x in range(self.dim_col)]
                prodcoeff = self.coeffs_field.zero
                for x in rowcol:
                    prodcoeff = self.coeffs_field.add(prodcoeff,x)
                row_tmp.append(prodcoeff)
            A_times_B.append(row_tmp)
        return FFMat(self.coeffs_field,A_times_B) 

    
    def mult_by_scalar(self,a):
        """ Multiplies a matrix by a scalar a.
            It returns an instance of FFMat.
        """
        a = self.coeffs_field.elt(a)
        new_row = []
        for row in self.coeffs:
            row_tmp = [self.coeffs_field.mult(x,a) for x in row]
            new_row.append(row_tmp)
        return FFMat(self.coeffs_field,new_row) 
    
    def exp(self,n):
        """ Computes the power of a matrix with coefficients in a finite field. 
        """
        assert (type(n) == int), "The exponent should be an intger."
        assert self.dim_col == self.dim_row, "The matrix should be square."
        M = self.coeffs_field.identity_matrix(self.dim_row)
        for i in range(n):
            M = M.mult(self)
        return M
    
    def gaussian_elimination(self):
        """ Performs Gaussian elimination, pseudo-code is taken from wikipedia 
        """
        A = copy.deepcopy(self.coeffs)
        #initial pivot row
        h = 0 
        #initial pivot column
        k = 0 
        while h < self.dim_row and k < self.dim_col: 
            #fin the kth pivot 
            colk = [row[k] for row in A[h:]]
            imax = colk.index(max(colk))+h
            if A[imax][k] == self.coeffs_field.zero:
                #no pivot in this column, tries next column
                k+=1
            else:
                A[h],A[imax] = A[imax],A[h]
                for i in range(h+1,self.dim_row):
                    f = self.coeffs_field.mult(A[i][k],self.coeffs_field.inverse_modp(A[h][k]))
                    A[i][k] = self.coeffs_field.zero
                    #for remaining elements in the current row
                    for j in range(k+1,self.dim_col):
                        A[i][j] = self.coeffs_field.subtract(A[i][j],self.coeffs_field.mult(A[h][j],f))
                h+=1
                k+=1
        return FFMat(self.coeffs_field,A)
        
    def det(self):
        """ Computes the determinant of a matrix with coefficients in a finite field. 
        """
        assert self.dim_row == self.dim_col, 'The matrix needs to be square.'
        ge = self.gaussian_elimination().coeffs
        det = self.coeffs_field.one
        for i in range(self.dim_col):
            det = self.coeffs_field.mult(det,ge[i][i])
        return det
    
    def inverse_modp(self):
        """ Computes the inverse of a matrix with coefficients in a finite field. 
        """
        assert self.dim_row == self.dim_col, 'Rectangle matrices are not invertible.'
        A = []
        #creates an augmented matrix
        for row in self.coeffs:
            row_tmp = [x for x in row]+[self.coeffs_field.zero for cnt in range(self.dim_row)]
            A.append(row_tmp)
        for i in range(self.dim_row):
            A[i][i+self.dim_col] = self.coeffs_field.one  
        #apply Gaussian elimination on the augmented matrix
        Agauss = FFMat(self.coeffs_field,A).gaussian_elimination().coeffs
        #puts 1 on the diagonal
        for i in range(self.dim_row):
            assert Agauss[i][i] != self.coeffs_field.zero, "The matrix is not invertible." 
            diaginv = self.coeffs_field.inverse_modp(Agauss[i][i])
            Agauss[i] = [self.coeffs_field.mult(Agauss[i][k],diaginv) for k in range(2*self.dim_col)]
        #puts 0 above the diagonal
        for j in range(self.dim_col-1,0,-1):
            for i in range(j-1,-1,-1):
                if Agauss[i][j] != self.coeffs_field.zero: 
                    Agauss[i] = [self.coeffs_field.subtract(Agauss[i][k],self.coeffs_field.mult(Agauss[j][k],Agauss[i][j])) for k in range(2*self.dim_col)]
        #removes the identity block on the left
        Ainv = []
        for row in Agauss:
            row_tmp = row[self.dim_col:]
            Ainv.append(row_tmp)
        
        return FFMat(self.coeffs_field,Ainv)
    

#----------------------------------------------------------#
#
# class EC
#
#----------------------------------------------------------#

class EC:
    """ Class to construct erasure codes over a finite field.
        It contains:    
        Internal functions:
        (a) generator_from_parity_check: computes a generator matrix upon instantiation
        (b) systematic_parity_check: computes a systematic parity check matrix upon instantiation
        External functions:
        (1) systematic_form: computes the systematic form of a matrix
        (2) minimum_distance: computes the minimum Hamming distance
        (3) repetition_code: constructs the repetition code 
        (4) parity_check_code: constructs the parity check code
        (5) Hamming code: constructs a Hamming code
        (6) is_perfect: computes the Sphere Packing Bound and checks if code is perfect
    """
    
    def __init__(self, finite_field,mat_coeffs,var):
        """ Takes a finite field, and a list as inputs, 
            the list contains the coefficients of either a kxn generator matrix (use var='G'), 
            or a (n-k)xn parity check matrix (use var='H').
            It is assumed to be a list of lists, containg the rows of the matrix.
        """
        #defines whether the coefficients live
        self.coeffs_field = finite_field
        
        condition1 = (type(mat_coeffs) == list and all(len(row) == len(mat_coeffs[0]) for row in mat_coeffs)) 
        assert condition1, "A matrix is described by a list of lists of equal size."
        assert var == 'G' or var == 'H' or var == 'name', "Specify G for generator matrix, H for parity check matrix, or 'name' to create a named code."
        
        #coefficients should be finite field elements
        mat_coeffs_ffelts = []
        for row in mat_coeffs:
            #this makes sure every entry is a finite field element (from the right finite field)
            mat_coeffs_ffelts.append([self.coeffs_field.elt(a) for a in row])
            
        if var == 'G':
            self.generator_matrix = self.systematic_form(mat_coeffs_ffelts)
            self.dim = len(self.generator_matrix.coeffs)
            self.length = len(mat_coeffs[0])
            self.parity_check_matrix = self.systematic_parity_check(self.generator_matrix)
        if var == 'H':
            self.length = len(mat_coeffs[0])
            self.generator_matrix = self.systematic_form(self.generator_from_parity_check(mat_coeffs_ffelts))
            self.dim = len(self.generator_matrix.coeffs)
            self.parity_check_matrix = self.systematic_parity_check(self.generator_matrix)
    

    def systematic_form(self,G):
        """ Computes the systematic form of a generator matrix with coefficients in a finite field.
            G is a list of lists.
        """
        n = len(G[0])
        #apply Gaussian elimination 
        Ggauss = FFMat(self.coeffs_field,G).gaussian_elimination().coeffs
        #removes all zero rows
        Ggauss = [row for row in Ggauss if not(row == [self.coeffs_field.zero for cnt in range(n)])]
        k = len(Ggauss)
        #set pivots to 1
        for i in range(k):
            coli = [Ggauss[i].index(elt) for elt in Ggauss[i] if elt != self.coeffs_field.zero][0]
            pivinv = self.coeffs_field.inverse_modp(Ggauss[i][coli])
            Ggauss[i] = [self.coeffs_field.mult(Ggauss[i][j],pivinv) for j in range(n)]
            
        cidx = 0
        ridx = 0
        while cidx < n and ridx < k:
            col = [Ggauss[row][cidx] for row in range(k)]
            ei = [self.coeffs_field.zero for cnt in range(k)]
            ei[ridx] = self.coeffs_field.one
            if col == ei:
                cidx += 1
                ridx += 1
            else: 
                if Ggauss[ridx][cidx] != self.coeffs_field.zero: 
                    #puts 0 above the diagonal
                    for i in range(ridx-1,-1,-1): 
                        Ggauss[i] = [self.coeffs_field.subtract(Ggauss[i][l],self.coeffs_field.mult(Ggauss[ridx][l],Ggauss[i][cidx])) for l in range(n)]
                    cidx += 1
                    ridx += 1
                else: 
                    cidx += 1
                    
        allcols = range(n)
        for i in range(k):
            #unit vector
            ei = [self.coeffs_field.zero for cnt in range(k)]
            ei[i] = self.coeffs_field.one
            idxi = [j for j in range(n) if (np.array(Ggauss)[:,j] == np.array(ei)).all()][0]
            if idxi != i: 
                #swap both columns
                for j in range(k): 
                    Ggauss[j][idxi],Ggauss[j][i] = Ggauss[j][i],Ggauss[j][idxi]
            
        return FFMat(self.coeffs_field,Ggauss)
    
    def generator_from_parity_check(self,H):
        """ Computes a generator matrix given a parity check matrix with coefficients in a finite field.
            H is a list of lists.
        """
        A = copy.deepcopy(H)
        #creates an augmented matrix
        for cnt in range(self.length):
            row_tmp = [self.coeffs_field.zero for cnts in range(self.length)]
            row_tmp[cnt] = self.coeffs_field.one  
            A.append(row_tmp)
        #apply Gaussian elimination on the augmented matrix
        Agauss = ((FFMat(self.coeffs_field,A).transpose()).gaussian_elimination()).transpose()
        n_min_k = len(H)
        basis_ker = []
        #detects zero columns in the upper part
        for col in range(self.length):
            if [Agauss.coeffs[row][col] for row in range(n_min_k)] == [self.coeffs_field.zero for cnt in range(n_min_k)]: 
                #extracts a basis from the kernel
                basis_ker.append([Agauss.coeffs[row][col] for row in range(n_min_k,len(A))])
        return basis_ker
    
    def systematic_parity_check(self,G):
        """ Computes a parity check matrix in systematic form given a generator matrix in systematic form.
            G is an FFMat instance.
        """
        A = []
        #extract the A part of [I_k A]
        for row in G.coeffs:
            A.append(row[self.dim:self.length])
        Atrans = (FFMat(self.coeffs_field,A).transpose()).coeffs
        Hsys = []
        for i in range(self.length-self.dim):
            row_tmp = [self.coeffs_field.subtract(self.coeffs_field.zero,x) for x in Atrans[i]]
            ei = [self.coeffs_field.zero for cnt in range(self.length-self.dim)]
            ei[i] = self.coeffs_field.one
            Hsys.append(row_tmp+ei)
        return FFMat(self.coeffs_field,Hsys)
    
    def minimum_distance(self):
        """ Computes the minimum Hamming distance of a code.
            Returns an integer.
            Algorithm 2.3 ``Searching for linear codes with large minimum distance"  by Markus Grassl
        """
        primelt = self.coeffs_field.primitive_elt()
        if self.coeffs_field.char == self.coeffs_field.size:
            Fqstar = range(1,self.coeffs_field.char)
        else:
            Fqstar = [self.coeffs_field.exp(primelt,i) for i in range(self.coeffs_field.size-1)]
        #initializes lower and upper bound
        dlb = 1
        dub = self.length-self.dim+1
        w = 1
        while w <= self.dim and dlb < dub: 
            minw = self.length
            #generates vectors of weight w
            ids = list(itertools.combinations(tuple(range(self.dim)), w))
            allcoeffs = [list(i) for i in itertools.product(Fqstar,repeat = w)]
            for idxs in ids:
                for coeffs in allcoeffs: 
                    x = [self.coeffs_field.zero for cnt in range(self.dim)]
                    cntcoeff = 0
                    for idx in idxs:
                        x[idx] = coeffs[cntcoeff]
                        cntcoeff += 1
                    c = FFMat(self.coeffs_field,[x]).mult(self.generator_matrix).coeffs 
                    wc = len([ci for ci in c[0] if ci != self.coeffs_field.zero])
                    if wc < minw:
                        minw = wc
            dub = min(dub,minw)
            dlb = w + 1
            w = w + 1
        return dub
    
    
    def repetition_code(self,n):
        """ Computes a repetition code of length n over Fq
        """
        assert type(n) == int, "The input should be an integer."
        return EC(self.coeffs_field, [[self.coeffs_field.one for cnt in range(n)]],'G')
     
    
    def parity_check_code(self,n):
        """ Computes a parity check code of length n over Fq
        """
        assert type(n) == int, "The input should be an integer."
        
        self.dim = n-1
        self.length = n
        G = []
        for i in range(n-1):
            ei = [self.coeffs_field.zero for cnt in range(n-1)]
            ei[i] = self.coeffs_field.one
            G.append(ei+[self.coeffs_field.one])
        return EC(self.coeffs_field,G,'G')
    
    
    def Hamming_code(self,r):
        """ Computes a Hamming code of dimension r over Fq
        """
        assert type(r) == int, "The input should be an integer."
        
        #generates the finite field
        primelt = self.coeffs_field.primitive_elt()
        if self.coeffs_field.char == self.coeffs_field.size:
            Fqstar = range(0,self.coeffs_field.char)
        else:
            Fqstar = [self.coeffs_field.exp(primelt,i) for i in range(self.coeffs_field.size-1)]+[self.coeffs_field.zero]
        #generates all vectors
        H = [list(i) for i in itertools.product(Fqstar,repeat = r)]
        H.remove([self.coeffs_field.zero for cnt in range(r)])
        #removes multiples
        for h in H:
            hmultiples = []
            for scalar in Fqstar:
                tmp = [self.coeffs_field.mult(hi,scalar) for hi in h]
                hmultiples.append(tmp)
            H = [x for x in H if not(x in hmultiples)]+[h]   
        Hpc = (FFMat(self.coeffs_field,H).transpose()).coeffs
        return EC(self.coeffs_field,Hpc,'H')
    
    def is_perfect(self):
        """ Computes the sphere packing bound and compares with the code.
             Returns a pair as outputs, the value of the sphere packing bound, 
             and a boolean, true if matches, false otherwise.
        """
        n = self.length
        k = self.dim
        q = self.coeffs_field.size 
        d = self.minimum_distance()
        t = int(floor((d-1)/2))
        is_perfect =  False
        den = 1
        for i in range(1,t+1):
            nchoosei = factorial(n)/(factorial(i)*factorial(n-i))
            den = den + nchoosei*((q-1)**i)
        spb = (q**n)/den
        if spb == q**k:
            is_perfect = True
        return spb,is_perfect

