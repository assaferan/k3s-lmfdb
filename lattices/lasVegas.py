import os
from functools import reduce

from sage.arith.misc import kronecker, prime_divisors
from sage.arith.functions import LCM_list
from sage.combinat.integer_vector_weighted import WeightedIntegerVectors
from sage.interfaces.magma import magma
from sage.matrix.constructor import matrix
from sage.structure.element import Matrix
from sage.misc.functional import is_even, is_odd
from sage.misc.misc_c import prod
from sage.quadratic_forms.genera.genus import Genus_Symbol_p_adic_ring
from sage.quadratic_forms.genera.genus import GenusSymbol_global_ring
from sage.rings.integer_ring import ZZ
from sage.rings.integer import Integer
from sage.modules.free_quadratic_module import FreeQuadraticModule_submodule_with_basis_pid, FreeQuadraticModule
from sage.modules.free_quadratic_module_integer_symmetric import IntegralLattice, local_modification
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.structure.factorization_integer import IntegerFactorization
from random import randint
from math import prod

def nonQuadraticResidue(p, randomThreshold = 40):
    """p: ODD prime
    randomThreshold: some positive integer
    Returns a non-quadratic residue (from 0 to p-1) modulo p
    Will return an error if number of attempts exceeds randomThreshold"""
    if p == 2:
        raise Exception("nonQuadraticResidue can't take p=2 as an argument")
    
    for i in range(randomThreshold):
        trialNum = randint(2,p-1) #random integer from 2 to p-1
        if kronecker(trialNum,p) == -1: #if it's a non-QR
            return trialNum
    raise Exception(f"Threshold of {randomThreshold} attempts exceeded in finding a non-QR modulo {p}")

def oddPrimeDiagonalRepresentative(globalGenus, p, k = None):
    """globalGenus: sage GenusSymbol_global_ring object
        p: ODD prime
        k: (optional, default None) positive integer
        
        finds a diagonalized quadratic form that matches the genus
        globalGenus at p, and outputs the k entries with lowest vp
        (or all entries if k = None)
        
        (Cases 1 and 2 of Lemma 17)
        
        used in 7.1, 7.2 and Thm 18"""

    returnList = [] #list of diagonal entries
    if globalGenus.determinant()%p == 0: #case 2
        nonQRmodp = nonQuadraticResidue(p)
        pAdicSymbolList = globalGenus.local_symbol(p).canonical_symbol() #.local_symbol(p) is a deepcopy, idk about optimization here bc we only need to be reading
        for constituent in pAdicSymbolList:
            coefficient = p**constituent[0]
            #each constituent f_q(x) will be a bunch of 1's followed by the nonQRmodp
            for i in range(constituent[1] - 1):
                returnList.append(coefficient)
            if constituent[2] != 1: #if the sign of the constituent is negative
                returnList.append(coefficient*nonQRmodp)
            else:
                returnList.append(coefficient)

            if k != None and len(returnList) >= k: #if we've found enough terms
                break
        return returnList
    
    else: #case 1
        dimension = globalGenus.dimension()
        if k!= None and k < dimension:
            return [1 for i in range(k)]
        return [1 for i in range(dimension - 1)] + [globalGenus.determinant()]

def dyadicBlockRepresentative(globalGenus):
    dyadicTupleList = globalGenus.local_symbol(2).symbol_tuple_list()
    blocks = []
    Tplus = matrix(ZZ, 2, 2, [2, 1, 1, 4]) #TODO: optimize by leaving these pre-defined
    Tminus = matrix(ZZ, 2, 2, [2, 1, 1, 2])
    binaryTypeIForms = {(1,0):[1,7],
                        (1,2):[1,1],
                        (1,6):[3,3],
                        (-1,2):[3,7],
                        (-1,4):[1,3],
                        (-1,6):[1,5]} #binaryTypeIForms[(eps,odt)]. Copied from table 1 pg. 15
    ternaryTypeIForms = {(1,1):[1,1,7],
                         (1,3):[1,1,1],
                         (1,5):[7,7,7],
                         (1,7):[1,7,7],
                         (-1,1):[3,3,3],
                         (-1,3):[3,3,5],
                         (-1,5):[1,1,3],
                         (-1,7):[1,1,5]}
    
    for constituent in dyadicTupleList:
        powTwo = 2**constituent[0]
        n = constituent[1]
        if constituent[2]%8 in [1,7]: #if eps = 1
            eps = 1
        else:
            eps = -1
        if constituent[3] == 0: #type II constituent
            assert n%2 == 0, f"constituent {constituent} has wrong dimension parity (type II but odd dimension)"
            for i in range(n//2 - 1):
                blocks.append(powTwo*Tplus)
            if eps == 1:
                blocks.append(powTwo*Tplus)
            else:
                blocks.append(powTwo*Tminus)

        else: #type I constituent
            if n == 1:
                blocks.append(matrix(ZZ,[[powTwo*constituent[4]]]))
            elif n == 2:
                assert (eps, constituent[4]) in binaryTypeIForms, "ieoa5iu nw4"
                blockToAdd = binaryTypeIForms[(eps, constituent[4])]
                for item in blockToAdd:
                    blocks.append(matrix(ZZ,[[powTwo*item]]))
            else:
                for i in range(n-3):
                    blocks.append(matrix(ZZ,[[powTwo]]))
                newOdt = (constituent[4]-(n-3))%8
                assert (eps, newOdt) in ternaryTypeIForms, "ieoa5iu nw4"
                blockToAdd = ternaryTypeIForms[(eps, newOdt)]
                for item in blockToAdd:
                    blocks.append(matrix(ZZ,[[powTwo*item]]))
    return blocks

def primitiveRepresentationTypeII(binaryTypeII, t):
    """binaryTypeII: two by two type II matrix"""
    l = binaryTypeII[1,0].valuation(2)
    reducedMatrix = binaryTypeII/2**l
    assert reducedMatrix[0,0] in ZZ
    assert reducedMatrix[1,1] in ZZ
    reducedT = t/2**l
    assert reducedT.valuation(2) == 1

    #TODO

def twoSquaresSumToNonsquare(primePower, nonsquare, randomThreshold = 40):
    """primePower: an ODD prime power
    nonsquare: quadratic non-residue modulo primePower 
    randomThreshold: some maximum number of times that the loop can fail

    returns (a, b) s.t. a^2 + b^2 == nonsquare (mod primePower)
    

    TODO might wanna cache this result since we're going to need it for later? probably not tho it takes literally no time
    """
    p, k = list(factor(primePower))[0]
    found = False
    for i in range(randomThreshold):
        a = randint(1, primePower)
        if kronecker(nonsquare-a**2,p) == 1:
            found = True
            break

    if not found:
        raise Exception(f"Threshold of {randomThreshold} attempts exceeded in finding two squares sum to {nonsquare}")
    R = Zmod(primePower)
    b = sqrt(R(nonsquare-a**2))
    return (a,b)


def primitiveRepresentationOddPrimes(tau1, tau2unreduced, p, tUnreduced, Kp):
    assert tau2unreduced.valuation(p) == tUnreduced.valuation(p)
    assert tau1.valuation(p) == 0
    i = tau2unreduced.valuation(p)
    assert i%2 == 0
    tau2= tau2/p**i
    t = tUnreduced/p**(tUnreduced.valuation(p))
    assert kronecker(t,p) != kronecker(tau1, p)

    pPower = p**Kp
    ZpKpZ = Zmod(pPower)
    ZpZ = Zmod(p)

    if kronecker(t,p) == kronecker(tau2,p):
        return (0,sqrt(ZpKpZ(t*inverse_mod(tau2,p**Kp))))
    
    y1, noty2 = twoSquaresSumToNonsquare(p, ZpZ(t)/ZpZ(tau1))
    y2 = noty2*sqrt(Zpz(tau1)/Zpz(tau2))
    
    
def crtMatrix(congruences):
    """congruences: List of ordered pairs (modulus, matrix mod modulus)"""
    modulus = LCM_list([i[0] for i in congruences])
    width = congruences[0][1].ncols()
    height = congruences[0][1].nrows()
    returnMatrix = zero_matrix(ZZ, height, width)
    for col in width:
        for row in height:
            returnMatrix[row, col] = crt([(congruences[i][0], congruences[i][1][row, col]) for i in range(len(congruences))])
    return returnMatrix

def bar(k):
    """k = integer or factorization object
    
    outputs integer bar(k): k but precision padded
    (i.e. if p^e was a component in the prime factorization
    of k before, the component in bar(k) is p^(e+k_p), where
    k_p = 1 if p!=2 and k_p = 3 if p=2.)
    
    Defined on pg. 8 of Dubey/Holenstein"""
    primeFactorization = list(factor(2*k))
    bark = k
    for pTuple in primeFactorization:
        if pTuple[0] == 2:
            bark *= 8
        else:
            bark *= pTuple[0]
    return bark

def cpr(n,p):
    return n//p**(n.valuation(p))

def reduceGenus(globalGenus):
    """globalGenus: sage GenusSymbol_global_ring object

    Returns pair (reduced_genus, gcd)

    reduced_genus = reduced version of genus (first constituent always has coefficient p^0)
    
    gcd = how much the genus was divided by"""

    det = globalGenus.determinant()
    signaturePair = globalGenus.signature_pair()
    relevantPrimes = ZZ(2*det).prime_divisors()

    genusGcd = 1
    newLocalSymbols = []
    for p in relevantPrimes:
        localAtp = globalGenus.local_symbol(p).symbol_tuple_list()
        # print(localAtp)
        multiplier = localAtp[0][0]
        for i in localAtp:
            i[0] -= multiplier #this feels cursed, but its fine bc symbol_tuple_list deepcopies
        genusGcd *= (p**multiplier)
        newLocalSymbols.append(Genus_Symbol_p_adic_ring(p, localAtp))

    return (GenusSymbol_global_ring(signaturePair, newLocalSymbols), genusGcd) #TODO: add representative too if we know the representative of the old one

def solveDirichlet(congruences, cut = 10000):
    #TODO
    """congruences: List of ordered pairs (modulus, residue)
    Returns a prime satisfying each congruence
    
    According to theorem 3, this algorithm should terminate in polynomial time"""
    modulus = LCM_list([i[0] for i in congruences])
    residue = crt(congruences)
    checkingNum = residue
    iterationCount = 0
    while (not checkingNum.is_prime()) and (iterationCount < cut): #guaranteed to terminate by dirichlet, guaranteed to terminate in n^3 time by theorem 3 apparently
        checkingNum += modulus
        iterationCount += 1
    if iterationCount == cut:
        raise Exception(f"Dirichlet theorem prime not found within first {cut} trials")
    return checkingNum

def getE2S2type(globalGenus):
    """globalGenus: sage GenusSymbol_global_ring object; degree at least 4
    
    Returns a tuple (e2, S2, type) for p=2 (see below)
    
    type = 2 if there is a type II block in S
    otherwise type = 1"""
    n = globalGenus.dimension()
    det = globalGenus.determinant()

    blockDiagonalList = dyadicBlockRepresentative(globalGenus) #sorted by rank already
    existsTypeIIblock = False
    for i, block in enumerate(blockDiagonalList):
        if block.nrows() == 2: #if constituent is type II
            existsTypeIIconstituent = True
            e2 = block[1,0].valuation(2) + 1
            
            blockDiagonalList.pop(i) #we're destined to return the function atp so this stuff doesn't matter
            blockDiagonalList.insert(0,block)

            return (e2, blockDiagonalList, 2)
        else: #all constituents are type I
            e2 = blockDiagonalList[3].valuation(2)

            firstFour = blockDiagonalList[:4] #as specified on pg 34
            return (e2, firstFour[::-1] + blockDiagonalList[4:], 1)

def primitivelyRepresentedTWithRepresentations(globalGenus):
    """globalGenus: sage GenusSymbol_global_ring object; degree at least 4
    
    Returns a tuple: (t,q,representations)
    t is an integer; it is a divisor (possibly negative)
    of det(globalGenus) that has a primitive representation
    under the genus

    q is an integer; q = bar(t^(n-1)*det(globalGenus)), where bar() denotes
    the precision-padded version of q
    TODO might wanna make q a factorization object for optimization purposes?

    representations is a list of tuples; each tuple is of the form (p,S,x,A)
        where p runs over all primes dividing representationPrecision
        S is the entire nxn block-diagonal matrix
        x is an array of n integers that primitively represent t
        over Z/p^(vp(q))Z (first four integers of n-tuple; rest are 0)
        A is the other (n-1)xn matrix (see pg 34)

    Transcribed from Lemma 26"""
    n = globalGenus.dimension()
    assert n > 3, "dimension must be at least 4"
    det = globalGenus.determinant()
    relevantOddPrimes = (2*globalGenus.determinant()).prime_divisors()[1:]
    oddPrimesDiagonal = [oddPrimeDiagonalRepresentative(globalGenus, p) for p in relevantOddPrimes]

    #step i: find e_{-1}
    if globalGenus.signature_pair()[0] == 0:
        multiplySign = -1 #(this is (-1)^e_{-1})
    else:
        multiplySign = 1

    #step ii: find parities
    eOddPrimesParities = []
    oddPrimesSelectedPair = []
    oddPrimeEqualPairValue = [] #not used now, used on step v
    oddPrimeEqualPairPrimePart = [] #not used now, used on step v
    #compute parities of e for odd primes
    for i in range(len(relevantOddPrimes)):
        p = relevantOddPrimes[i]
        pFirstThreeTerms = oddPrimesDiagonal[i]
        values = [pFirstThreeTerms[j].valuation(p) for j in range(3)]

        #determine the parity of e for each odd prime
        if values[0]%2 == values[1]%2: #testing for the majority parity
            eOddPrimesParities.append(values[0]%2)
            oddPrimeEqualPairValue.append((values[0], values[1]))
            oddPrimeEqualPairPrimePart.append((pFirstThreeTerms[0]//p**values[0],pFirstThreeTerms[1]//p**values[1]))
            oddPrimesSelectedPair.append((0,1))
        elif values[0]%2 == values[2]%2:
            eOddPrimesParities.append(values[0]%2)
            oddPrimeEqualPairValue.append((values[0], values[2]))
            oddPrimeEqualPairPrimePart.append((pFirstThreeTerms[0]//p**values[0],pFirstThreeTerms[2]//p**values[2]))
            oddPrimesSelectedPair.append((0,2))
        else:
            eOddPrimesParities.append(values[1]%2)
            oddPrimeEqualPairValue.append((values[1],values[2]))
            oddPrimeEqualPairPrimePart.append((pFirstThreeTerms[1]//p**values[1],pFirstThreeTerms[2]//p**values[2]))
            oddPrimesSelectedPair.append((1,2))
    
    #step iii: compute e_2
    e2, S2, repType = getE2S2type(globalGenus)
    
    #step iv: compute r
    r = prod([relevantOddPrimes[i]**eOddPrimesParities[i] for i in range(len(relevantOddPrimes))]) * multiplySign * 2**(e2%2)
    eOddPrimes = []
    SOddPrimes = []

    #step v: compute e_p for odd primes p
    oddPrimeRepresentedByFirstEntry=[]
    for i, p in enumerate(relevantOddPrimes):
        tau = oddPrimeEqualPairPrimePart[i][0]
        cprR = r//p**eOddPrimesParities[i]
        diagonal = oddPrimesDiagonal[i]

        if kronecker(tau,p) == kronecker(cprR,p):
            eOddPrimes.append(oddPrimeEqualPairValue[i][0]) #set e_p := i_a
            oddPrimeRepresentedByFirstEntry.append(True)

            firstEntryIndex = oddPrimesSelectedPair[0]
            firstEntry = diagonal[firstEntryIndex] #could do assert tau = firstEntry
            diagonal.pop(firstEntryIndex)
            diagonal.insert(0,firstEntry)

            SOddPrimes.append(diagonal_matrix(ZZ, diagonal))
        else:
            eOddPrimes.append(oddPrimeEqualPairValue[i][1]) #set e_p := i_b
            oddPrimeRepresentedByFirstEntry.append(False)

            opsp = oddPrimesSelectedPair[i]
            if opsp[i] == (0,1):
                missing = 2
            elif opsp[i] == (1,2):
                missing = 0
            else:
                missing = 1
            newdiagonal = [diagonal[opsp[1]], diagonal[opsp[0]], diagonal[missing]] + diagonal[3:]

            SOddPrimes.append(diagonal_matrix(ZZ, newdiagonal))

    #step vi: finish
    t =  prod([p**eOddPrimes[i] for i,p in enumerate(relevantOddPrimes)]) * multiplySign * 2**(eTwo%2)

    representations = []
    #lol jk step 68: find x, A for p = 2

    #lol jk step 69: find x, A for odd primes p
    for i, p in enumerate(relevantOddPrimes):
        S = SOddPrimes[i]
        Kp = eOddPrimes[i]*(n-1)+det.valuation(p)+1
        if oddPrimeRepresentedByFirstEntry[i]: #if we can represent w/ first entry in S
            firstVar = sqrt_mod(t*inverse_mod(S[0],p**Kp),p**Kp)
            x = matrix(ZZ,[[x]]+[[0] for i in range(n-1)])
            Atop = matrix(ZZ, [[0 for i in range(n)]])
            Abottom = diagonal_matrix(ZZ, [inverse_mod(x)]+[1 for i in range(n-1)])
            A = block_matrix([[Atop],
                              [Abottom]])
        else: #we can represent w/ first two entries in S
            d1 = S[0]
            d2 = S[1]

        representations.append((p, S, x, A))

    return (t, bar(t**(n-1)*det), representations)

def primitivelyRepresentedIntegerAlmostDividingDetForRankThree(globalGenus):
    """globalGenus: sage GenusSymbol_global_ring object with dimension three
    
    Returns an integer divisor (possibly negative) of det(globalGenus)
    that has a primitive representation under the genus

    Transcribed from Lemma 27"""

    assert globalGenus.dimension() == 3, "wrong dimension"
    relevantOddPrimes = globalGenus.determinant().prime_divisors()
    oddPrimesDiagonalForm = [oddPrimeDiagonalRepresentative(globalGenus, p) for p in relevantOddPrimes]

    #step i: find e_{-1}
    if globalGenus.signature_pair()[0] == 0:
        multiplySign = -1 #(this is (-1)^e_{-1})
    else:
        multiplySign = 1

    #step ii: find parities
    eOddPrimesParities = []
    oddPrimeEqualPairValue = [] #not used now, used on step v
    oddPrimeEqualPairPrimePart = [] #not used now, used on step v
    #compute parities of e for odd primes
    for i in range(len(relevantOddPrimes)):
        p = relevantOddPrimes[i]
        pFirstThreeTerms = oddPrimesDiagonalForm[i]
        values = [oddPrimesDiagonalForm[i][j].valuation(p) for j in range(3)]

        #determine the parity of e for each odd prime
        if values[0]%2 == values[1]%2: #testing for the majority parity
            eOddPrimesParities.append(values[0]%2)
            oddPrimeEqualPairValue.append((values[0], values[1]))
            oddPrimeEqualPairPrimePart.append((pFirstThreeTerms[0]//values[0],pFirstThreeTerms[1]//values[1]))
        elif values[0]%2 == values[2]%2:
            eOddPrimesParities.append(values[0]%2)
            oddPrimeEqualPairValue.append((values[0], values[2]))
            oddPrimeEqualPairPrimePart.append((pFirstThreeTerms[0]//values[0],pFirstThreeTerms[2]//values[2]))
        else:
            eOddPrimesParities.append(values[1]%2)
            oddPrimeEqualPairValue.append((values[1],values[2]))
            oddPrimeEqualPairPrimePart.append((pFirstThreeTerms[1]//values[1],pFirstThreeTerms[2]//values[2]))

    #step iii: compute e_2 in easy case, there exists a type II block
    twoAdicSymbolList = globalGenus.local_symbol(2).canonical_symbol()
    existsTypeIIconstituent = False
    for constituent in twoAdicSymbolList:
        if constituent[3] == 0: #if constituent is type II
            existsTypeIIconstituent = True
            eTwo = constituent[0] + 1
            break

    #step iv: if no type II block was found in step iii, compute e_2 now
    fancyP = 1 #we will multiply t by "fancyP" always, so set it to 1 if unnecessary
    if not existsTypeIIconstituent: #all constituents are type I
        #TODO
        fancyP = 69
        eTwo = 420

    #step v: compute r
    r = prod([relevantOddPrimes[i]**eOddPrimesParities[i] for i in range(len(relevantOddPrimes))]) * multiplySign * 2**(eTwo%2) * fancyP
    eOddPrimes = []

    #step vi: compute e_p for odd primes p
    for i, p in enumerate(relevantOddPrimes):
        tau = oddPrimeEqualPairPrimePart[i][0]
        cprR = r//p**eOddPrimesParities[i]
        if kronecker(tau,p) == kronecker(cprR,p):
            eOddPrimes.append(oddPrimeEqualPairValue[i][0]) #set e_p := i_a
        else:
            eOddPrimes.append(oddPrimeEqualPairValue[i][1]) #set e_p := i_b

    #step vii: finish
    return prod([p**eOddPrimes[i] for p,i in enumerate(relevantOddPrimes)]) * multiplySign * 2**(eTwo%2)

def primitivelyRepresentedIntegerAlmostDividingDetForRankTwoTypeII(globalGenus):
    """globalGenus: sage GenusSymbol_global_ring object with dimension three
    
    Returns an integer divisor (possibly negative) of det(globalGenus)
    that has a primitive representation under the genus

    Transcribed from Lemma 30
    
    **Genus must be reduced and type II for this one!**"""

    assert globalGenus.dimension() == 2, "wrong dimension"
    oddPrimitiveTest = [globalGenus.local_symbol(p).canonical_symbol()[0][0] == 0 \
                        for p in globalGenus.determinant().prime_divisors()] #first constitutent has coefficient p^0
    evenPrimitiveTest = globalGenus.local_symbol(2).canonical_symbol()[0][3] == 0 #first (only) constituent is even
    assert all(oddPrimitiveTest) and evenPrimitiveTest, "not a reduced symbol"

    def ap(p):
        return globalGenus.local_symbol(p).canonical_symbol()[0][2]

    # if globalGenus.determinant() > 0:
    #     eps = 1
    # else:
    #     eps = -1
    
    if globalGenus.signature_pair()[0] == 0:
        rho = -1
    else:
        rho = 1
    det = globalGenus.determinant().prime_divisors()

    setS = [p for p in det.prime_divisors() \
            if p!=2 and globalGenus.local_symbol(p).canonical_symbol()[-1][0]%2 == 1] #definition of S on p. 25
    setSsub = [[[p for p in setS if p%8 == d and kronecker(ap(p), p) == sign] \
                for sign in [1,-1]] for d in [1,3,5,7]]
    
    fancyPcongruences = [(2*rho*ap(p), p) for p in setS]
    if (rho == 1 and len(setSsub[1][0]) + len(setSsub[1][1]) + \
                    len(setSsub[2][0]) + len(setSsub[2][1]) + \
                    len(setSsub[0][1]) + len(setSsub[1][1]) + \
                    len(setSsub[0][2]) + len(setSsub[0][3]) %2 == 1) or \
                    (rho == -1 and len(setSsub[2][0]) + len(setSsub[2][1]) + \
                    len(setSsub[3][0]) + len(setSsub[3][1]) + \
                    len(setSsub[0][1]) + len(setSsub[1][1]) + \
                    len(setSsub[0][2]) + len(setSsub[0][3]) %2 == 1):
        fancyPcongruences.append((1,4))
    else:
        fancyPcongruences.append((3,4))
    
    fancyP = solveDirichlet(fancyPcongruences)

    rSquared = prod([p**(globalGenus.local_symbol(p).canonical_symbol()[-1][0]) \
              for p in det.prime_divisors() \
              if (p!=2) and (not p in setS) and (kronecker(ap(p), p) != kronecker(2*rho*fancyP, p))])
    
    return 2*rho*fancyP*rSquared

def primitivelyRepresentedIntegerAlmostDividingDetForRankTwoTypeIEven(globalGenus):
    assert globalGenus.dimension() == 2, "wrong dimension"
    oddPrimitiveTest = [globalGenus.local_symbol(p).canonical_symbol()[0][0] == 0 \
                        for p in globalGenus.determinant().prime_divisors()] #first constitutent has coefficient p^0
    evenPrimitiveTest = globalGenus.local_symbol(2).canonical_symbol()[0][3] == 0 #first (only) constituent is even
    assert all(oddPrimitiveTest) and evenPrimitiveTest, "not a reduced symbol"
    
    def ap(p):
        return globalGenus.local_symbol(p).canonical_symbol()[0][2]
    
    def bp(p):
        return globalGenus.local_symbol(p).canonical_symbol()[-1][2]

    if globalGenus.determinant() > 0:
        eps = 1
    else:
        eps = -1
    
    if globalGenus.signature_pair()[0] == 0:
        rho = -1
    else:
        rho = 1
    det = globalGenus.determinant().prime_divisors()

    setS = [p for p in det.prime_divisors() \
            if p!=2 and globalGenus.local_symbol(p).canonical_symbol()[-1][0]%2 == 1] #definition of S on p. 25
    setSsub = [[[p for p in setS if p%8 == d and kronecker(ap(p), p) == sign] \
                for sign in [1,-1]] for d in [1,3,5,7]]
    
    fancyPcongruences = [(rho*ap(p), p) for p in setS]

    X = [rho*ap(2)%8, rho*bp(2)%8]
    x = 0
    if 1 in X:
        x = 1
    if 5 in X:
        x = 5
    if x != 0:
        pass
    else:
        y = 0
        if 3 in X:
            y = 3
        if 7 in X:
            y = 7
        
        assert y!= 0, "impossibility"
        fancyPcongruences.append((y,8))

def primitivelyRepresentedIntegerAlmostDividingDetForRankTwoTypeIOdd(globalGenus):
    assert globalGenus.dimension() == 2, "wrong dimension"
    oddPrimitiveTest = [globalGenus.local_symbol(p).canonical_symbol()[0][0] == 0 \
                        for p in globalGenus.determinant().prime_divisors()] #first constitutent has coefficient p^0
    evenPrimitiveTest = globalGenus.local_symbol(2).canonical_symbol()[0][3] == 0 #first (only) constituent is even
    assert all(oddPrimitiveTest) and evenPrimitiveTest, "not a reduced symbol"

def findChangeOfBasisModPrimePower(p, k, M1, M2):
    """p is a prime
    k is a positive integer exponent
    M1 is a square matrix of some rank n
    M2 is a square matrix of rank n (same as M1)
    
    returns a matrix U s.t. U^T M1 U == M2 (mod p^k)"""




def dubeyHolensteinLatticeRepresentative(globalGenus):
    """globalGenus: sage GenusSymbol_global_ring object

    Returns a lattice in the genus
    """

    n = globalGenus.dimension()
    det = globalGenus.determinant()
    if det ==0:
        raise Exception("help")
    signaturePair = globalGenus.signature_pair()

    if n<=3:
        return globalGenus.representative() #TODO lol oops
    
    reducedGenus, gcdOfGenus = reduceGenus(globalGenus)
    relevantPrimes = (2*det).prime_divisors()

    t,q,representations = primitivelyRepresentedTWithRepresentations(reducedGenus)
    localSyms = []
    for representation in representations:
        p = representation[0]
        S = representation[1]
        x = representation[2]
        A = representation[3]
        d = x.transpose()*S*A
        H = t*A.transpose()*S*A - d.transpose()*d
        localSyms.append(LocalGenusSymbol(H,p))

    if t > 0:
        assert signaturePair[0] >= 1, "t has wrong sign"
        newSignaturePair = (signaturePair[0]-1, signaturePair[1])
    else:
        assert signaturePair[0] >= 1, "t has wrong sign"
        newSignaturePair = (signaturePair[1], signaturePair[0]-1)

    newGenus = GenusSymbol_global_ring(newSignaturePair, localSyms)
    Hstar = dubeyHolensteinLatticeRepresentative()

    Hstar.append()

    return reducedGenus

if __name__ == "__main__":
    # A = matrix(ZZ, 5, 5, [4, 2, 3, 4, 10,
    #                       2, 4, 6, 8, 10,
    #                       3, 6, 6, 12, 15,
    #                       4, 8, 12, 8, 20,
    #                       10, 10, 15, 20, 10])
    # A = matrix(ZZ, 5, 5, [6, 0, 0, 1, 4,
    #                       0, 12, 0, 3, 0,
    #                       0, 0, 18, 0, 0,
    #                       1, 3, 0, 24, 0,
    #                       4, 0, 0, 0, 30])


    # A = matrix(ZZ, [[64,0,0,0,0,0,0,0,4],
    #                 [0,2,0,2,0,1,0,3,0],
    #                 [0,0,3,0,0,0,0,0,0],
    #                 [0,2,0,4,0,1,0,1,0],
    #                 [0,0,0,0,5,0,0,0,0],
    #                 [0,1,0,1,0,6,0,2,0],
    #                 [0,0,0,0,0,0,7,0,0],
    #                 [0,3,0,1,0,2,0,8,0],
    #                 [4,0,0,0,0,0,0,0,4]])
    # inputGenus = Genus(A)
    # print(f"INPUT GENUS: {inputGenus} \n_________")
    # dyadicRep = block_diagonal_matrix(dyadicBlockRepresentative(inputGenus))
    # print(Genus(dyadicRep))

    print(factor(625))
    print(twoSquaresSumToNonsquare(625,69))


    # print(f"OUTPUT: {dubeyHolensteinLatticeRepresentative(inputGenus)} \n_________")




#T+ = (2 1 // 1 4),
#T- = (2 1 // 1 2)