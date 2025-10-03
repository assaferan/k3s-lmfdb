from sage.rings.finite_rings.integer_mod_ring import Zmod
from sage.rings.integer_ring import ZZ
from sage.all import QQ

from sage.arith.misc import kronecker, inverse_mod, factor, gcd
from sage.arith.functions import LCM_list
from sage.arith.all import crt

from sage.functions.other import ceil
from sage.misc.functional import sqrt
from sage.misc.misc_c import prod

from sage.matrix.constructor import matrix, zero_matrix
from sage.matrix.special import block_diagonal_matrix, diagonal_matrix, block_matrix

from sage.quadratic_forms.genera.genus import Genus, Genus_Symbol_p_adic_ring, GenusSymbol_global_ring, LocalGenusSymbol, is_GlobalGenus
from sage.quadratic_forms.genera.normal_form import p_adic_normal_form

from sage.libs.pari import pari
from sage.quadratic_forms.quadratic_form import QuadraticForm

from functools import reduce
from pathlib import Path
from random import randint
from math import prod
from itertools import product
from sage.env import SAGE_EXTCODE

def symbolList(globalGenus):
    return ("\n".join([f"({i.prime()},\t{i.symbol_tuple_list()})," for i in globalGenus.local_symbols()]))[:-1]
def genusFromSymbolLists(signaturePair, tupleLists):
    """tupleLists: list of pairs (p, tupleList)"""
    return GenusSymbol_global_ring(signaturePair, [Genus_Symbol_p_adic_ring(i[0], i[1]) for i in tupleLists])
def genusKey(globalGenus):
    return (globalGenus.signature_pair(), tuple((local.prime(), tuple(tuple(constituent) for constituent in local.symbol_tuple_list())) for local in globalGenus.local_symbols()))

def matrix_entries_gcd(M):
    entries = [abs(int(e)) for e in M.list() if e != 0]
    return reduce(gcd, entries, 0)
def genusOrder(globalGenus):
    return prod([i.prime()**i.symbol_tuple_list()[-1][0] for i in globalGenus.local_symbols()])

def makeSmall(L, signaturePair=None):
    """does LLL on the matrix L of integers
    signaturePair can be calculated off of L but im lazy"""
    if signaturePair == None:
        sig = matrix_signature_pair(L)
    else:
        sig = signaturePair
    if sig[0] * sig[1] != 0:
        m = pari(L)
        pari.read(Path(SAGE_EXTCODE) / "pari" / "simon" / "qfsolve.gp")
        m = pari('qflllgram_indefgoon')(m)
        # convert the output string to sage
        returnL = m.sage()[0]
        U = m.sage()[1]
    elif sig[1] != 0:
        U = -(-L).LLL_gram()
        returnL = U.T * L * U
    else:
        U = L.LLL_gram()
        returnL = U.T * L * U
    return returnL, U

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

def matrix_signature_pair(M):
    """
    Return the signature pair (n_pos, n_neg) of a symmetric matrix M
    over QQ or ZZ. Zero eigenvalues are ignored.
    """
    Q = QuadraticForm(QQ, M)
    s = Q.signature()
    r = M.rank()
    n_pos = (r + s) // 2
    n_neg = (r - s) // 2
    return (n_pos, n_neg)

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

def primitiveRepresentationTypeII(binaryTypeII, tUnreduced, kUnreduced):
    """binaryTypeII: two by two type II matrix
    tUnreduced: integer
    kUnreduced: positive integer

    returns primitive representation of unreducedT by binaryTypeII mod 2^unreducedK as a pair (x1,x2)
    
    see lemma 17 of DH14b"""
    l = binaryTypeII[1,0].valuation(2)+1
    reducedMatrix = binaryTypeII/2**l
    assert reducedMatrix[0,0] in ZZ
    assert reducedMatrix[1,1] in ZZ
    a = reducedMatrix[0,0]
    b = 2*reducedMatrix[1,0]
    c = reducedMatrix[1,1]
    t = tUnreduced/2**l
    k = kUnreduced - l
    assert k>0
    assert t.valuation(2) == 0

    #variables are now as written in lemma 17 of DH14b

    #determine parities of x1,x2 as a1, a2
    if a%2 == c%2: #x+1+x == 1 (mod 2)
        y1 = ZZ(1)
        y2 = ZZ(1)
    elif a%2 == 1: #1+0+0 == 1 (mod 2)
        y1 = ZZ(1)
        y2 = ZZ(0)
    else: #0+0+1 == 1 (mod 2)
        y1 = ZZ(0)
        y2 = ZZ(1)

    if y1 == 1:
        for i in range(1,k):
            #right now, (y1,y2) represents t mod 2^i, so we need to lift so it represents mod 2^(i+1)
            y2 += (t-(a*y1*y1 + b*y1*y2 + c*y2*y2)) % 2**(i+1)
    elif y1 == 0:
        for i in range(1,k):
            y1 += (t-(a*y1*y1 + b*y1*y2 + c*y2*y2)) % 2**(i+1)
    

    value = binaryTypeII[0,0]*y1**2 + binaryTypeII[0,1]*2*y1*y2 + binaryTypeII[1,1]*y2**2
    assert (value - tUnreduced)%2**kUnreduced == 0, \
        f"Wrong representation, {binaryTypeII[0,0]}*{y1}^2 + {2*binaryTypeII[0,1]}*{y1}*{y2} + {binaryTypeII[1,1]}*{y2}^2 == {value} (mod 2^{kUnreduced}), expected {tUnreduced}"
    return (y1,y2)

def twoSquaresSumToNonsquare(primePower, nonsquare, randomThreshold = 40):
    """primePower: an ODD prime power
    nonsquare: quadratic non-residue modulo primePower 
    randomThreshold: some maximum number of times that the loop can fail

    returns (a, b) s.t. a^2 + b^2 == nonsquare (mod primePower)
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

def theorem10Lift(Q, t, x, p, i, k):
    """Q = gram matrix of quadratic form
    x = n-dimensional vector of integers (matrix type_)
    p = prime
    t = integer
    i = s.t. p^i is initial precision of representation
    k = required outputted precision
    
    outputs an n-dimensional p^k vector that is a p^k representation of t"""
    if k<i:
        return x
    a = (x.transpose()*Q*x)[0,0]
    R = Zmod(p**k)
    u = sqrt(R(t/a))
    result = u*x
    # assert R(t) == (result.transpose()*matrix(R, Q)*result)[0,0], f"{R(t)} =/= {(result.transpose()*matrix(R, Q)*result)[0,0]} (mod {p}^{k})"
    return u*x

def primitiveRepresentationOddPrimes(tau1, tau2unreduced, tUnreduced, p, Kp):
    """tau1 = element of Z/(Kp)Z with valuation 0
    tau2unreduced = element of Z/(Kp)Z with even valuation
    tUnredeuced = element of Z/(Kp)Z with same valuation as tau2unreduced, also prime part of tUnreduced has opposite legendre as tau1
    p = some prime
    Kp = integer

    Returns a tuple pair (x1,x2) such that tUnreduced = (tau1)(x1^2) + (tau2unreduced)(x2^2)

    See lemma 25
    """
    assert tau2unreduced.valuation(p) == tUnreduced.valuation(p)
    assert tau1.valuation(p) == 0
    i = tau2unreduced.valuation(p)
    assert i%2 == 0
    assert i < Kp, "valuation of tau2 is too high"
    tau2= tau2unreduced/p**i
    t = tUnreduced/p**(tUnreduced.valuation(p))
    assert kronecker(t,p) != kronecker(tau1, p)

    pPower = p**Kp
    ZpKpZ = Zmod(pPower)
    ZpZ = Zmod(p)

    if kronecker(t,p) == kronecker(tau2,p):
        return (0,sqrt(ZpKpZ(t)/ZpKpZ(tau2)))
    
    y1, noty2 = twoSquaresSumToNonsquare(p, ZpZ(t)/ZpZ(tau1))
    y2 = noty2*sqrt(ZpZ(tau1)/ZpZ(tau2))

    x1, x2 = ZZ(y1*p**(i/2)), ZZ(y2)
    assert((tau1*x1**2 + tau2unreduced*x2**2 - tUnreduced)%p**(i+1) == 0)

    form = matrix(ZZ, [[tau1, 0],
                        [0, tau2unreduced]])
    rep = matrix(ZZ, [[x1],
                      [x2]])
    liftedPair = theorem10Lift(form, tUnreduced, rep, p, i+1, Kp)
    lx1, lx2 = ZZ(liftedPair[0,0]), ZZ(liftedPair[1,0])

    total = (tau1*lx1**2 + tau2unreduced*lx2**2) % p**(Kp)
    assert (total - tUnreduced)%p**(Kp) == 0, \
        f"Incorrectly generated primitive representation: {tau1}*{lx1}^2 + {tau2unreduced}*{lx2}*2 == {total} (mod {p}^{Kp}), \n\
            expected {tUnreduced}"
    return (lx1,lx2)

def primitiveRepresentationFourTypeI(tauUnreduced, tUnreduced, k):
    """tauUnreduced: list of four integers tau1, ..., tau4 s.t. v2(tau1)≤v2(tau2)≤v2(tau3)≤v2tau(4)
    kUnreduced: positive integer
    
    see lemma 24"""
    i = [entry.valuation(2) for entry in tauUnreduced]
    tau = [entry/2**i[j] for j, entry in enumerate(tauUnreduced)]
    assert i[0] <= i[1] <= i[2] <= i[3]
    t = tUnreduced/2**i[3]
    assert t.valuation(2) == 0

    reducedCoefficients = [2**((i[3]-i[j])%2) * tau[j] for j in range(3)]+[tau[3]]
    reducedK = k/2**(i[3])
    allReps = list(product(*[[0,1,2,3],[0,1,2,3],[0,1,2,3],[1,3]]))
    repFound = False
    for reducedRep in allReps:
        if (sum([reducedCoefficients[j]*reducedRep[j]**2 for j in range(4)]) - t)%16 == 0:
            repFound = True
            break
    assert repFound, f"exhaustive search failed: no valid representation of {reducedCoefficients} (mod 16) found"
    assert (sum([reducedCoefficients[j]*reducedRep[j]**2 for j in range(4)])-t)%16 ==0, f"Wrong reduced representation"

    repList = [reducedRep[j]*2**ceil((i[3]-i[j])/2) for j in range(3)]+[reducedRep[3]]

    form = matrix(ZZ, [[2**i[0]*tau[0], 0, 0, 0],
                       [0, 2**i[1]*tau[1], 0, 0],
                       [0, 0, 2**i[2]*tau[2], 0],
                       [0, 0, 0, 2**i[3]*tau[3]]])
    rep = matrix(ZZ, [[repList[j]] for j in range(4)])

    
    unreducedRep = theorem10Lift(form, tUnreduced, rep, 2, i[3]+4, k)
    assert (sum([tauUnreduced[j]*unreducedRep[j,0]**2 for j in range(4)])-tUnreduced)%(2**k) == 0, f"Representation of \n{unreducedRep} is wrong."

    return [unreducedRep[j,0] for j in range(4)]

def crtMatrix(congruences):
    """congruences: List of ordered pairs (modulus, matrix mod modulus)"""
    modulus = LCM_list([i[0] for i in congruences])
    width = congruences[0][1].ncols()
    height = congruences[0][1].nrows()
    returnMatrix = zero_matrix(ZZ, height, width)
    for col in range(width):
        for row in range(height):
            returnMatrix[row, col] = crt([congruences[i][1][row, col] for i in range(len(congruences))], [congruences[i][0] for i in range(len(congruences))])
    return returnMatrix

def getGCD(globalGenus):
    det = globalGenus.determinant()
    genusGcd = 1
    relevantPrimes = ZZ(2*det).prime_divisors()
    for p in relevantPrimes:
        localAtp = globalGenus.local_symbol(p).symbol_tuple_list()
        genusGcd *= p**localAtp[0][0] #exponent of p in the first constituent
    return genusGcd

def divideByGCD(localGenus, p, GCD):
    tupleList = localGenus.symbol_tuple_list()
    pPart = GCD.valuation(p)
    rest = GCD/p**pPart
    if p != 2: #for odd primes
        toggleDeterminantSign = kronecker(rest, p)
        for constituent in tupleList:
            constituent[0] -= pPart #reduce exponents of p in each constituent
            constituent[2] *= toggleDeterminantSign**constituent[1] #potentially need to flip the sign of the constituent
    else: #p = 2
        for constituent in tupleList:
            constituent[0] -= pPart
            constituent[2] = ZZ(Zmod(8)(constituent[2]/rest**constituent[1]))
            constituent[4] = ZZ(Zmod(8)(constituent[4]/rest))
    return tupleList

def reduceGenus(globalGenus):
    """globalGenus: sage GenusSymbol_global_ring object

    Returns pair (reduced_genus, gcd)

    reduced_genus = reduced version of genus (first constituent always has coefficient p^0)
    
    gcd = how much the genus was divided by"""

    det = globalGenus.determinant()
    signaturePair = globalGenus.signature_pair()
    relevantPrimes = ZZ(2*det).prime_divisors()

    GenusGCD = getGCD(globalGenus)
    newLocalSymbols = [Genus_Symbol_p_adic_ring(p, divideByGCD(globalGenus.local_symbol(p), p, GenusGCD)) \
                       for p in relevantPrimes]

    return (GenusSymbol_global_ring(signaturePair, newLocalSymbols), GenusGCD) #TODO: add representative too if we know the representative of the old one

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

def computeChangeOfVariables(Htild, H, q):
    """returns a matrix U such that Htild == U^T HU (mod q)"""
    crtList = []
    for p, e in q.factor():
        m = p**e
        H1 = matrix(ZZ,matrix(Zmod(m),H))
        Htild1 = matrix(ZZ,matrix(Zmod(m),Htild))
        D1, U1 = p_adic_normal_form(H1,p, precision=e)
        D2, U2 = p_adic_normal_form(Htild1,p, precision=e)
        assert D1 == D2, f"Inputted forms are not isomorphic modulo {p}^{e}."
        U = U1.transpose()*U2.transpose().inverse()
        crtList.append((m, matrix(ZZ,U)))

    returnU = crtMatrix(crtList)
    # assert matrix(Zmod(q), returnU.transpose()*H*returnU) == matrix(Zmod(q), Htild)
    return returnU

def getE2S2type(globalGenus):
    """globalGenus: sage GenusSymbol_global_ring object; degree at least 4
    
    Returns a tuple (e2, S2, type) for p=2 (see below)
    
    type = 2 if there is a type II block in S
    otherwise type = 1"""
    n = globalGenus.dimension()
    det = globalGenus.determinant()
    blockDiagonalList = dyadicBlockRepresentative(globalGenus) #sorted by rank already
    existsTypeIIconstituent = False
    for i, block in enumerate(blockDiagonalList):
        if block.nrows() == 2: #if constituent is type II
            existsTypeIIconstituent = True

            a = block[0,0]
            b = block[1,0]
            c = block[1,1]
            e2 = b.valuation(2) + 1

            if a.valuation(2) > c.valuation(2):
                block[0,0] = c
                block[1,1] = a
            
            blockDiagonalList.pop(i) #we're destined to return the function atp so this stuff doesn't matter
            blockDiagonalList.insert(0,block)

            return (e2, blockDiagonalList, 2)
    if not existsTypeIIconstituent: #all constituents are type I
        e2 = blockDiagonalList[3][0,0].valuation(2)
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
    e2, S2list, repType = getE2S2type(globalGenus)
    S2 = block_diagonal_matrix(S2list)
    
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

            firstEntryIndex = oddPrimesSelectedPair[i][0]
            firstEntry = diagonal[firstEntryIndex] #could do assert tau = firstEntry
            diagonal.pop(firstEntryIndex)
            diagonal.insert(0,firstEntry)

            SOddPrimes.append(diagonal_matrix(ZZ, diagonal))
        else:
            eOddPrimes.append(oddPrimeEqualPairValue[i][1]) #set e_p := i_b
            oddPrimeRepresentedByFirstEntry.append(False)

            opsp = oddPrimesSelectedPair[i]
            if opsp == (0,1):
                missing = 2
            elif opsp == (1,2):
                missing = 0
            else:
                missing = 1
            newdiagonal = [diagonal[opsp[1]], diagonal[opsp[0]], diagonal[missing]] + diagonal[3:]

            SOddPrimes.append(diagonal_matrix(ZZ, newdiagonal))

    #step vi: finish
    t =  prod([p**eOddPrimes[i] for i,p in enumerate(relevantOddPrimes)]) * multiplySign * ZZ(2)**e2

    representations = []
    #find x, A for p = 2
    K2 = e2*(n-1)+det.valuation(2)+3
    if repType == 2:
        x1, x2 = primitiveRepresentationTypeII(S2list[0], t, K2)
        x = matrix(ZZ, [[x1],[x2]]+[[0] for i in range(n-2)])
        Atop = matrix(ZZ, [[0 for i in range(n-1)]])
        Abottom = diagonal_matrix(ZZ, [inverse_mod(x1, 2**K2)]+[1 for i in range(n-2)])
        A2 = block_matrix([[Atop],
                         [Abottom]])
    else:
        x1, x2, x3, x4 = primitiveRepresentationFourTypeI([i[0,0] for i in S2list[:4][::-1]], t, K2)
        x = matrix(ZZ, [[x4],[x3],[x2],[x1]]+[[0] for i in range(n-4)])
        Atop = matrix(ZZ, [[0 for i in range(n-1)]])
        Abottom = diagonal_matrix(ZZ, [inverse_mod(x4, 2**K2)]+[1 for i in range(n-2)])
        A2 = block_matrix([[Atop],
                         [Abottom]])
        
    assert matrix(Zmod(2**K2),x.transpose()*S2*x)[0,0] == Zmod(2**K2)(t)
    assert block_matrix(Zmod(2**K2),[[x,A2]]).determinant() == Zmod(2**K2)(1)

    representations.append((ZZ(2), S2, x,A2))

    #find x, A for odd primes p
    for i, p in enumerate(relevantOddPrimes):
        S = SOddPrimes[i]
        Kp = eOddPrimes[i]*(n-1)+det.valuation(p)+1
        R = Zmod(p**Kp)
        if oddPrimeRepresentedByFirstEntry[i]: #if we can represent w/ first entry in S
            # print(f"t: {t}, p: {p}, S:\n{S}")
            firstVar = ZZ(sqrt(R(t/S[0,0])))
            x = matrix(ZZ,[[firstVar]]+[[0] for i in range(n-1)])
            Atop = matrix(ZZ, [[0 for i in range(n-1)]])
            Abottom = diagonal_matrix(ZZ, [ZZ(R(1)/R(firstVar))]+[1 for i in range(n-2)])
            A = block_matrix([[Atop],
                              [Abottom]])
        else: #we can represent w/ first two entries in S
            d1 = S[0,0]
            d2 = S[1,1]
            commonFactor = p**d2.valuation(p)
            x2,x1 = primitiveRepresentationOddPrimes(d2/commonFactor, d1/commonFactor, t/commonFactor, p, Kp)
            x = matrix(ZZ, [[x1],[x2]]+[[0] for i in range(n-2)])
            Atop = matrix(ZZ, [[0 for i in range(n-1)]])
            Abottom = diagonal_matrix(ZZ, [ZZ(R(1)/R(x1))]+[1 for i in range(n-2)])
            A = block_matrix([[Atop],
                              [Abottom]])

        assert matrix(R,x.transpose()*S*x)[0,0] == R(t)
        block_matrix(R,[[x,A]]).determinant()
        assert block_matrix(R,[[x,A]]).determinant() == R(1)
        representations.append((p, S, x, A))

    return (t, bar(t*det), representations)

def dubeyHolensteinLatticeRepresentative(globalGenus, check=False, superDumbCheck=False, depth=1, cache=None):
    """globalGenus: sage GenusSymbol_global_ring object

    Returns a lattice in the genus

    check, superDumbCheck: debugging stuff. check should always be false unless debugging one case (i think is_GlobalGenus has some bugs), superDumbCheck checks some more stuff in between
    depth: debugging stuff too, serves no actual purpose in the code right now
    """
    if check:
        assert is_GlobalGenus(globalGenus)

    #check cache
    if not (cache is None):
        if genusKey(globalGenus) in cache:
            return cache[genusKey(globalGenus)]

    n0 = globalGenus.dimension()
    det = globalGenus.determinant()
    assert det != 0

    reducedGenus, gcdOfGenus = reduceGenus(globalGenus)
    if check:
        assert is_GlobalGenus(reducedGenus)
    
    moreReducedGenus = removeTrivialTerms(reducedGenus)
    n = moreReducedGenus.dimension()
    addBack = block_diagonal_matrix([matrix([[1]])]*(n0-n))
    signaturePair = moreReducedGenus.signature_pair()

    if n<=3:
        preliminary = moreReducedGenus.representative() #TODO lol oops
        returnMatrix = gcdOfGenus*(block_diagonal_matrix([addBack,preliminary]))
        assert Genus(returnMatrix) == globalGenus
        return returnMatrix
    
    det = moreReducedGenus.determinant()
    t,q,representations = primitivelyRepresentedTWithRepresentations(moreReducedGenus)
    localSyms = []

    dCongruenceList = []
    hCongruenceList = []
    for representation in representations:
        p = representation[0]
        Sp = representation[1]
        xp = representation[2]
        Ap = representation[3]
        dp = xp.transpose()*Sp*Ap #TODO: return matrices in Z/p^kZ as to make these numbers managably sized
        Hp = t*Ap.transpose()*Sp*Ap - dp.transpose()*dp
        # if depth == 20:
        #     print(f"p: {p}\nx:\n{xp}\n\nA:\n{Ap}\n\nS:\n{Sp}\n\nd:\n{dp}\n\nH:\n{matrix(Zmod(p**(q.valuation(p))), Hp)}\n\n")
        #     print("_________________")
        localSyms.append(LocalGenusSymbol(Hp,p))
        dCongruenceList.append((p**(q.valuation(p)), dp))
        hCongruenceList.append((p**(q.valuation(p)), Hp))
    d = crtMatrix(dCongruenceList)
    H = crtMatrix(hCongruenceList)

    if t > 0:
        assert signaturePair[0] >= 1
        newSignaturePair = (signaturePair[0]-1, signaturePair[1])
    else:
        assert signaturePair[1] >= 1
        newSignaturePair = (signaturePair[1]-1,signaturePair[0])

    newGenus = GenusSymbol_global_ring(newSignaturePair, localSyms)
    if check:
        assert is_GlobalGenus(newGenus) #check if new genus has rep
    Htild = dubeyHolensteinLatticeRepresentative(newGenus, check, superDumbCheck, depth+1, cache)
    Utild = computeChangeOfVariables(Htild, H, q)

    bottomRight = (Htild+Utild.transpose()*d.transpose()*d*Utild)/t
    returnMatrixBlock = block_matrix([[t, d*Utild],
                                      [(d*Utild).transpose(), bottomRight]])
    returnMatrix = makeSmall(matrix(gcdOfGenus*block_diagonal_matrix(addBack,returnMatrixBlock)),
                             signaturePair)[0]

    assert Genus(returnMatrix) == globalGenus, f"Bad output. Generated representative's genus:\n{Genus(returnMatrix)}\n...versus input genus:\n{globalGenus}"
    
    if not (cache is None):
        cache[genusKey(globalGenus)] = returnMatrix #update to cache
    return returnMatrix

def removeTrivialTerms(globalGenus):
    """if the forms start with a bunch of diagonal terms, we can delete them from every symbol and add them at the end"""
    localSyms = globalGenus.local_symbols()
    n_plus = globalGenus.signature_pair()[0]
    n_minus = globalGenus.signature_pair()[1]
    availableTerms = []
    for i in localSyms:
        firstTuple = i.symbol_tuple_list()[0]
        if firstTuple[0] != 0: #no p^0 constituent altogether, we can't do anything
            return globalGenus
        if i.prime() != 2: #odd symbol
            if firstTuple[2] == 1: #if determinant = 1
                availableTerms.append(firstTuple[1])
            else:
                availableTerms.append(firstTuple[1]-1)
        else: #dyadic symbol
            rank, det, s, oddity = firstTuple[1:]
            if s == 0: #if type II, we can't do anything
                return globalGenus
            maxTermsOff = rank-3 #maxTermsOff is maximum number of diagonal 1's
            #rules from conway sloane p383
            if det in [1,7]:
                if (oddity-rank)%8 in [0,6]:
                    maxTermsOff = rank-1
                elif (oddity-rank)%8 == 4:
                    maxTermsOff = rank-2
            else: #det in [3,5]
                if (oddity-rank)%8 in [2,4]:
                    maxTermsOff = rank-1
                elif (oddity-rank)%8 == 0:
                    maxTermsOff = rank-2

            if maxTermsOff == -1: #this is trigerred if rank is 2 and we can't have diagonal 1's:
                return globalGenus
            
            availableTerms.append(maxTermsOff)
    availableTerms.append(n_plus) #can't have more 1's on the diagonal than positive terms in signature

    numTermsCut = min(availableTerms)
    signaturePair = (n_plus-numTermsCut,n_minus) #new signature
    tupleList = [[i.prime(),i.symbol_tuple_list()] for i in localSyms]
    for localSymbol in tupleList:
        localSymbol[1][0][1] -= numTermsCut
        if localSymbol[0] == 2: #if p=2
            localSymbol[1][0][4] = (localSymbol[1][0][4]-numTermsCut)%8 #update oddity too
        if localSymbol[1][0][1] == 0: #if rank 0 term
            localSymbol[1].pop(0) #just get rid of it
    return genusFromSymbolLists(signaturePair, tupleList)

if __name__ == "__main__":
    #TEST IF FUNCTION WORKS
    A = matrix(ZZ, [[69,0,0,0,0,0,0,0,4],
                    [0,5,0,2,0,1,0,3,0],
                    [0,0,3,0,0,0,0,0,0],
                    [0,2,0,4,0,1,0,1,0],
                    [0,0,0,0,5,0,0,0,0],
                    [0,1,0,1,0,6,0,2,0],
                    [0,0,0,0,0,0,7,0,0],
                    [0,3,0,1,0,2,0,8,0],
                    [4,0,0,0,0,0,0,0,420]])
    
    B = matrix(ZZ, 5, 5, [6, 0, 0, 1, 4,
                          0, 12, 0, 3, 0,
                          0, 0, 18, 0, 0,
                          1, 3, 0, 24, 0,
                          4, 0, 0, 0, 30])
    
    C = matrix(ZZ, [[2,0,0,0,0],
                    [0,14,2,-6,-6],
                    [0,2,80,12,-30],
                    [0,-6,12,144,-6],
                    [0,-6,-30,-6,270]])
    
    D = matrix(ZZ, [[2,0,0,0],
                    [0,14,2,-6],
                    [0,2,80,12],
                    [0,-6,12,144]])
    
    single = matrix(ZZ,[[1]])

    E = block_diagonal_matrix([single,single,single,single,D,D])

    inputGenus = Genus(E)
    reducedGenus = removeTrivialTerms(inputGenus)
    print(f"before:\n{inputGenus}")
    print(f"{symbolList(inputGenus)}\n___________")    
    print(f"after:\n{reducedGenus}")
    print(symbolList(reducedGenus))
    addBackTerms = inputGenus.dimension() - reducedGenus.dimension()
    addBack = block_diagonal_matrix([single]*addBackTerms+[reducedGenus.representative()])
    assert Genus(addBack) == inputGenus, f"After modifications:\n{symbolList(Genus(addBack))}"