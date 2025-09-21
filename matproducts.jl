using MATLAB
mat"addpath('Please enter path to your intlab file')"
mat"startintlab"
function _matprod(A,B) #For Real matrix products
    #Ensure to have started Intlab
    Ai = inf.(A)
    As = sup.(A)
    Bi = inf.(B)
    Bs = sup.(B)
    d = mat"infsup($Ai,$As)*infsup($Bi,$Bs)"
    return interval(d["inf"],d["sup"])
end

function _matprod2(A,B)
    dom = domain(B)
    codom = codomain(A)
    A = coefficients(A)
    B = coefficients(B)
    #Ensure to have started Intlab
    Ai = inf.(A)
    As = sup.(A)
    Bi = inf.(B)
    Bs = sup.(B)
    d = mat"infsup($Ai,$As)*infsup($Bi,$Bs)"
    return LinearOperator(dom,codom,interval(d["inf"],d["sup"]))
end


function spec_norm(A) #For Real matrix spectral norm
    #Ensure to have started Intlab
    if sup(maximum(abs.(imag.(A))))>0
        A = _cmatprod(A,A')
        A = real.(A)
        Ai = inf.(A)
        As = sup.(A)
        d = mat"norm(infsup($Ai,$As),2)"
        return sqrt(interval(d["inf"],d["sup"]))
    else 
        A = real.(A)
        Ai = inf.(A)
        As = sup.(A)
        d = mat"norm(infsup($Ai,$As),2)"
        return interval(d["inf"],d["sup"])
    end
end

function _cmatprod(A,B) #For complex matrix products
    #Ensure to have started Intlab
    Air = inf.(real(A))
    Aii = inf.(imag(A))
    Asr = sup.(real(A))
    Asi = sup.(imag(A))
    Bir = inf.(real(B))
    Bii = inf.(imag(B))
    Bsr = sup.(real(B))
    Bsi = sup.(imag(B))
    dr = mat"infsup($Air,$Asr)*infsup($Bir,$Bsr) - infsup($Aii,$Asi)*infsup($Bii,$Bsi)"
    di = mat"infsup($Aii,$Asi)*infsup($Bir,$Bsr) + infsup($Air,$Asr)*infsup($Bii,$Bsi)"
    return interval(dr["inf"],dr["sup"]) + interval(1im*di["inf"],1im*di["sup"])
end

function _cmatprod2(A,B) #For products of LinearOperators in RadiiPolynomial.jl
    dom = domain(B)
    codom = codomain(A)
    A = coefficients(A)
    B = coefficients(B)
    #Ensure to have started Intlab
    Air = inf.(real(A))
    Aii = inf.(imag(A))
    Asr = sup.(real(A))
    Asi = sup.(imag(A))
    Bir = inf.(real(B))
    Bii = inf.(imag(B))
    Bsr = sup.(real(B))
    Bsi = sup.(imag(B))
    dr = mat"infsup($Air,$Asr)*infsup($Bir,$Bsr) - infsup($Aii,$Asi)*infsup($Bii,$Bsi)"
    di = mat"infsup($Aii,$Asi)*infsup($Bir,$Bsr) + infsup($Air,$Asr)*infsup($Bii,$Bsi)"
    return LinearOperator(dom,codom,interval(dr["inf"],dr["sup"]) + interval(1im*di["inf"],1im*di["sup"]))
end