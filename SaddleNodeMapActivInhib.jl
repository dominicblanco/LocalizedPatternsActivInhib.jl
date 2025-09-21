# Computer assisted proof of saddle node bifurcations for a general class of 1D Activiator-Inhibitor models of the form 
# ∂ₜu = δ² Δu - cu + dv + u²v + a 
# ∂ₜv = Δv + hu - jv - u²v + b 
# (u,v) = (u(x,t),v(x,t))
# The following code computes the solution and rigorously proves Theorems 5.9 and 6.6 in Sections 5.3 and 6.2 of
# "Proving the existence of localized patterns and saddle node bifurcations in 1D activiator-inhibitor type models"  D. Blanco, M. Cadiot, and D. Fassler

#####################################################################################################################################################################

# Needed packages
using RadiiPolynomial, LinearAlgebra, JLD2
include("matproducts.jl")
#####################################################################################################################################################################


#################################### List of the needed functions : go directly to line 214 for the main code ################################################# 

# Performs the estimate of Lemma 4.1
function φ(A,B,C,D)
    O₁ = max(A,D) + max(B,C)
    O₂ = sqrt(A^2 + D^2 + B^2 + C^2)
    return min(O₁,O₂)
end

function _conv_small(u,v,N)
    #Computes u*v only up to order N
    order_u = order(space(u))[1]
    order_v = order(space(v))[1]
    C = Sequence(CosFourier(N,frequency(u)[1]), interval.((zeros(N+1))))
for i ∈ 0:N
    #@show i
    Cᵢ = interval(zero(Float64))
    for j ∈ max(i-order_u, -order_v):min(i+order_u, order_v)
        tu = abs(i-j)
        tv = abs(j)
        Cᵢ += u[tu] * v[tv]
    end
    C[i] = Cᵢ
end
    return C
end

#Builds Matrix P for trace
function trace2(N)
    P = Int.(zeros(N+1,N+1))
    P[2:end,2:end] = Matrix(I,N,N)
for n = 1:N
    P[1,n+1] = (Int(-2*(-1)^n))
end
    return P
end

# Computes the roots of the polynomial ax² + bx + c
function quad_roots(a, b, c)
    D = b^2 - interval(4)*a*c
    if sup(D) < 0
        D = Complex(D)
        sqrtD = sqrt(D)
        return [(-b + sqrtD) / (interval(2)*a), (-b - sqrtD) / (interval(2)*a)]
    else
        sqrtD = sqrt(D)
        return [(-b + sqrtD) / (interval(2)*a), (-b - sqrtD) / (interval(2)*a)]
    end
end

function integral_computation(ν, ν₁, ν₂, ν₃)
    # This function computes the integral squared of $\frac{(a₁ξ² + a₂)²}{l_{den}(ξ)^2}$

    # Compute roots of l_den
    y₁², y₂² = Complex.(quad_roots(interval(2π)^4*ν, interval(2π)^2*(ν*ν₂ - ν₁), -ν₂*(ν₁ + ν₃)))
    y₁ = sqrt(Complex(y₁²))
    y₂ = sqrt(Complex(y₂²))

    if sup(imag(y₁)) < 0
        y₁ = -y₁
    elseif sup(imag(y₂)) < 0
        y₂ = -y₂
    end

    residue_y₁(a1, a2) = interval(2)*(a1*y₁^2 + a2)*(interval(4)*a1*y₁^2*(y₁^2 - y₂^2) - (a1*y₁^2 + a2)*(interval(5)*y₁^2 - y₂^2)) / (interval(2^3) * interval(2π)^8 * ν^2 * y₁^3*(y₁^2 - y₂^2)^3)
    residue_y₂(a1, a2) = interval(2)*(a1*y₂^2 + a2)*(interval(4)*a1*y₂^2*(y₂^2 - y₁^2) - (a1*y₂^2 + a2)*(interval(5)*y₂^2 - y₁^2)) / (interval(2^3) * interval(2π)^8 * ν^2 * y₂^3*(y₂^2 - y₁^2)*(y₂^2 - y₁^2)*(y₂^2 - y₁^2))
    
    # Compute the integrals
    resl11_1 = residue_y₁(-interval(2π)^2*ν, ν₁)
    resl11_2 = residue_y₂(-interval(2π)^2*ν, ν₁)

    int_l11_squared = interval(2π*1im)*(resl11_1 + resl11_2)
    if inf(abs(imag(int_l11_squared))) == 0
        int_l11_squared = real(int_l11_squared)
    else
        error("Integral l11 has significant imaginary part")
    end

    resl12_1 = residue_y₁(interval(0), ν₂)
    resl12_2 = residue_y₂(interval(0), ν₂)

    int_l12_squared = interval(2π*1im)*(resl12_1 + resl12_2)
    if inf(abs(imag(int_l12_squared))) == 0
        int_l12_squared = real(int_l12_squared)
    else
        error("Integral l12 has significant imaginary part")
    end

    resl21_1 = residue_y₁(interval(0), ν₃)
    resl21_2 = residue_y₂(interval(0), ν₃)

    int_l21_squared = interval(2π*1im)*(resl21_1 + resl21_2)
    if inf(abs(imag(int_l21_squared))) == 0
        int_l21_squared = real(int_l21_squared)
    else
        error("Integral l21 has significant imaginary part")
    end

    resl22_1 = residue_y₁(-interval(2π)^2, -ν₂)
    resl22_2 = residue_y₂(-interval(2π)^2, -ν₂)

    int_l22_squared = interval(2π*1im)*(resl22_1 + resl22_2)
    if inf(abs(imag(int_l22_squared))) == 0
        int_l22_squared = real(int_l22_squared)
    else
        error("Integral l22 has significant imaginary part")
    end

    return int_l11_squared, int_l12_squared, int_l21_squared, int_l22_squared
end

# This computes generally one of the four terms needed to compute ||𝓁⁻¹||_ℳ₁
function _compute_ℳ₁_component(a₁,a₂,ν,ν₁,ν₂,ν₃,f_num,f_denom)
    f(ξ) = f_num(ξ)/f_denom(ξ)
    b₁ = ν
    b₂ = ν*ν₂-ν₁
    b₃ = -ν₂*(ν₁+ν₃)
    r₁,r₂ = quad_roots(ExactReal(16)*interval(π^4)*a₁*b₁,ExactReal(8)*interval(π^2)*a₂*b₁,a₂*b₂ - a₁*b₃)
    max_val = abs(f(interval(0)))
    if inf(r₁) > 0
        max_val = max(max_val,abs(f(sqrt(r₁))),abs(f(-sqrt(r₁))))
    end
    if inf(r₂) > 0
        max_val = max(max_val,abs(f(sqrt(r₂))),abs(f(-sqrt(r₂))))
    end
    return max_val
end

# Computes the constants Cⱼ and a of Lemma 4.6.
function _compute_C_a(νi,ν₁i,ν₂i,ν₃i)
    if sup((νi*ν₂i - ν₁i)^2 + ExactReal(4)*νi*ν₂i*(ν₁i + ν₃i)) < 0
        y = sqrt( (ν₁i - ν₂i*νi + interval(1im)*sqrt(-(νi*ν₂i - ν₁i)*(νi*ν₂i - ν₁i) - ExactReal(4)*νi*ν₂i*(ν₁i + ν₃i))) /(ExactReal(2)*νi))*ExactReal(1)/interval(2π)
        z₁ = ExactReal(2π)*interval(1im)*y
        z₂ = ExactReal(-2π)*interval(1im)*conj(y)
        if (sup(real(z₁)) < 0) & (sup(real(z₂)) < 0)
            z₁ = -z₁
            z₂ = -z₂ 
        end
    elseif isstrictless(sqrt((νi*ν₂i - ν₁i)*(νi*ν₂i - ν₁i) + ExactReal(4)*νi*ν₂i*(ν₁i + ν₃i)),  νi*ν₂i - ν₁i)
        z₁ = sqrt( (νi*ν₂i - ν₁i + sqrt((νi*ν₂i - ν₁i)*(νi*ν₂i - ν₁i) + ExactReal(4)*νi*ν₂i*(ν₁i + ν₃i))) / (ExactReal(2)*νi))
        z₂ = sqrt( (νi*ν₂i - ν₁i - sqrt((νi*ν₂i - ν₁i)*(νi*ν₂i - ν₁i) + ExactReal(4)*νi*ν₂i*(ν₁i + ν₃i))) / (ExactReal(2)*νi))
    else
        error(`Assumption 1 is not satisfied`)
    end

    _Cj(d₁, d₂, νi, ν₁i, ν₂i, ν₃i) = (abs(d₁*z₂) + abs(d₂ / z₂)) / abs(ExactReal(2) * νi * (z₁*z₁ - z₂*z₂))
    C1 = _Cj(ExactReal(-1), -ν₂i, νi, ν₁i, ν₂i, ν₃i)
    C2 = _Cj(interval(0), ν₂i, νi, ν₁i, ν₂i, ν₃i)
    C3 = _Cj(interval(0), ν₃i, νi, ν₁i, ν₂i, ν₃i)
    C4 = _Cj(-νi, ν₁i, νi, ν₁i, ν₂i, ν₃i)
    a = min(real(z₁), real(z₂))

    return a,C1,C2,C3,C4
end

# Computes the term || [-|2πξ|² 0 ; 0 0] 𝓁⁻¹||_ℳ₁ needed for the 𝒵₂ bound.
function _𝒵₂₁_ℳ₁_bound(ν,ν₁,ν₂,ν₃,l₁₂,l₂₂,l_den)
    # First entry 
    _first_entry = abs(l₁₂(interval(0))/l_den(interval(0)))
    r1 = (-ν₂*(ν₁+ν₃)/interval(16π^4))^interval(1/4)
    r2 = -(-ν₂*(ν₁+ν₃)/interval(16π^4))^interval(1/4)
    if inf(abs(imag(r1))) == 0
        _first_entry = max(_first_entry,abs(interval(4π^2)*r1^2*l₁₂(r1)/l_den(r1)))
    elseif inf(abs(imag(r2))) == 0 
        _first_entry = max(_first_entry,abs(interval(4π^2)*r2^2*l₁₂(r2)/l_den(r2)))
    end
    _second_entry = max(ExactReal(1)/ν,abs(l₂₂(interval(0))/l_den(interval(0)))) 
    r1²,r2² = Complex.(quad_roots(interval(16π^4)*ν*ν₂ - interval(16π^4)*ν₁-interval(16π^4)*ν, -interval(8π^2)*ν₂*ν₃-interval(8π^2)*ν₁*ν₂,-ν₂*ν₃-ν₁*ν₂))
    r1 = sqrt(r1²)
    r2 = -sqrt(r1²)
    r3 = sqrt(r2²)
    r4 = -sqrt(r2²)
    if inf(abs(imag(r1))) == 0
        _second_entry = max(_second_entry,abs(interval(4π^2)*r1^2*l₁₂(r1)/l_den(r1)))
    elseif inf(abs(imag(r2))) == 0 
        _second_entry = max(_second_entry,abs(interval(4π^2)*r2^2*l₁₂(r2)/l_den(r2)))
    elseif inf(abs(imag(r3))) == 0 
        _second_entry = max(_second_entry,abs(interval(4π^2)*r3^2*l₁₂(r3)/l_den(r3)))
    elseif inf(abs(imag(r4))) == 0 
        _second_entry = max(_second_entry,abs(interval(4π^2)*r4^2*l₁₂(r4)/l_den(r4)))
    end
    return sqrt(_first_entry^2 + _second_entry^2)
end

# Checks the conditions of the Radii-Polynomial Theorem (see Section 5).
function CAP(𝒴₀,𝒵₁,𝒵₂)
    if 𝒵₁ > 1
        display("Z₁ is too big")
        return 𝒵₁
    elseif 2𝒴₀*𝒵₂ > (1-𝒵₁)^2
        display("The condition 2𝒴₀*𝒵₂ < (1-𝒵₁)² is not satisfied")
        return 𝒴₀,𝒵₁,𝒵₂
    else
        display("The computer assisted proof was successful!")
        return 𝒴₀,𝒵₁,𝒵₂
    end
end

################### PROOF OF SOLUTIONS : MAIN CODE #################################################################################################################################################
# Candidate Solution
X = load("X_saddle","X")
N₀ = 800
N = 620
# Parameters
δ = sqrt(component(X,1)[1]) ; δi = interval(δ)    
c = 1 ; ci = interval(c)
b = 0.4154639603133325
d = 0.21
j = d
a = 0
h = 0 ; hi = interval(h)
r₀ = interval(4e-8) # value of r₀ for 𝒵₂

λ₁ = (a+b)/(c-h)
λ₂ = (c*λ₁ - a)/(λ₁^2 + d)

ν = δ^2 ; ν̄_interval = interval(ν) ; νi = interval(ν)
ν₁ = 2λ₁*λ₂ - c ; ν₁i = interval(ν₁)
ν₂ = d + λ₁^2 ; ν₂i = interval(ν₂)
ν₃ = h - 2λ₁*λ₂ ; ν₃i = interval(ν₃)
ν₄ = λ₂; ν₄i = interval(ν₄)
ν₅ = 2λ₁ ; ν₅i = interval(ν₅)

U = component(X,2)
V = component(X,3)
W₁ = component(X,4)
W₂ = component(X,5)
# Change of variable
U₁ = U - λ₁ 
U₂ = V - λ₂
W₁ = W₁ - λ₁
W₂ = W₂ - λ₂

d = π / (frequency(U)) ; di = interval(d) # Domain size
fouriero = CosFourier(N,π/d) 
fourier = CosFourier(N, π/di) # Fourier basis
fourier0 = CosFourier(N₀,π/di)
fourier_4 = fourier × fourier × fourier × fourier 
fourier0_4 = fourier0 × fourier0 × fourier0 × fourier0 
pfourier = ParameterSpace() × fourier × fourier × fourier × fourier 
pfourier0 = ParameterSpace() × fourier0 × fourier0 × fourier0 × fourier0 

𝒫 = LinearOperator(fourier0,fourier0,interval.(trace2(N₀)))
# Computing the trace discussed in Section 3.2.
Ū₁_interval = Sequence(fourier0, coefficients(𝒫)*interval.(coefficients(U₁)))
Ū₂_interval = Sequence(fourier0, coefficients(𝒫)*interval.(coefficients(U₂)))
W̄₁_interval = Sequence(fourier0, coefficients(𝒫)*interval.(coefficients(W₁)))
W̄₂_interval = Sequence(fourier0, coefficients(𝒫)*interval.(coefficients(W₂)))
X̄_interval = Sequence(pfourier0, [ν̄_interval ; Ū₁_interval[:] ; Ū₂_interval[:] ; W̄₁_interval[:] ; W̄₂_interval[:]])

# Building the Linear Operator l defined in Section 1.2.
@info "Building the Linear Operator"
l = LinearOperator(fourier^2, fourier^2, interval.(zeros(2*(N+1),2*(N+1)))) # Linear operator
project!(component(l, 1, 1), project(Derivative(2), fourier, fourier,Interval{Float64})*ν̄_interval + UniformScaling(interval(1)) * ν₁i)
project!(component(l, 1, 2), UniformScaling(interval(1)) * ν₂i)
project!(component(l, 2, 1), UniformScaling(interval(1)) * ν₃i)
project!(component(l, 2, 2), project(Derivative(2), fourier, fourier,Interval{Float64}) - UniformScaling(interval(1)) * ν₂i)

# Building the Linear Operator L defined in Section 5.
L = LinearOperator(pfourier,pfourier, interval.(zeros(1 + 4*(N+1),1+4*(N+1))))
L[1,1] = interval(1)
project!(component(L,2:3,2:3), l)
project!(component(L,4:5,4:5),l)

# Building a version of l and L on the space with N₀ coefficients.
l_long = LinearOperator(fourier0^2, fourier0^2, interval.(zeros(2*(N₀+1),2*(N₀+1)))) # Linear operator
project!(component(l_long, 1, 1), project(Derivative(2), fourier0, fourier0,Interval{Float64})*ν̄_interval + UniformScaling(interval(1)) * ν₁i)
project!(component(l_long, 1, 2), UniformScaling(interval(1)) * ν₂i)
project!(component(l_long, 2, 1), UniformScaling(interval(1)) * ν₃i)
project!(component(l_long, 2, 2), project(Derivative(2), fourier0, fourier0,Interval{Float64}) - UniformScaling(interval(1)) * ν₂i)
L_long = LinearOperator(pfourier0,pfourier0, interval.(zeros(1 + 4*(N₀+1),1+4*(N₀+1))))

L_long[1,1] = interval(1)
project!(component(L_long,2:3,2:3), l_long)
project!(component(L_long,4:5,4:5),l_long)
# Building the inverse Linear operators l⁻¹ and L⁻¹

l₁₁c = diag(coefficients(component(l,1,1)))
l₁₂c = diag(coefficients(component(l,1,2)))
l₂₁c = diag(coefficients(component(l,2,1)))
l₂₂c = diag(coefficients(component(l,2,2)))
l_denc = l₁₁c.*l₂₂c - l₂₁c.*l₁₂c
l⁻¹ = LinearOperator(fourier×fourier,fourier×fourier, [Diagonal(l₂₂c./l_denc) Diagonal(-l₁₂c./l_denc) ; Diagonal(-l₂₁c./l_denc) Diagonal(l₁₁c./l_denc)])

L⁻¹ = LinearOperator(pfourier,pfourier, interval.(zeros(1+4*(N+1),1+4*(N+1))))
L⁻¹[1,1] = interval(1) 
project!(component(L⁻¹,2:3,2:3), l⁻¹)
project!(component(L⁻¹,4:5,4:5), l⁻¹)

# Computation of B defined in Section 5.1.
@info "Building the B operator"
V₁_interval = ExactReal(2)*Ū₁_interval*Ū₂_interval + ExactReal(2)*ν₄i*Ū₁_interval + ν₅i*Ū₂_interval
V₂_interval = Ū₁_interval^2 + ν₅i*Ū₁_interval

Q₁ = ExactReal(2)*Ū₂_interval + ExactReal(2)*ν₄i
Q₂ = ExactReal(2)*Ū₁_interval + ν₅i

V₃_interval = Q₁*W̄₁_interval + Q₂*W̄₂_interval
V₄_interval = Q₂*W̄₁_interval
𝕍₁ᴺ = project(Multiplication(V₁_interval) ,fourier, fourier, Interval{Float64})
𝕍₂ᴺ = project(Multiplication(V₂_interval) ,fourier, fourier, Interval{Float64})
𝕍₃ᴺ = project(Multiplication(V₃_interval) ,fourier, fourier, Interval{Float64})
𝕍₄ᴺ = project(Multiplication(V₄_interval) ,fourier, fourier, Interval{Float64})

W̄_interval = Sequence(fourier×fourier, [coefficients(project(copy(W̄₁_interval),fourier)) ; coefficients(project(copy(W̄₂_interval),fourier))])
ξ₁ = component(l⁻¹*W̄_interval,1)
ξ₂ = component(l⁻¹*W̄_interval,2)
ξ = Sequence(fourier×fourier, [coefficients(ξ₁) ; coefficients(ξ₂)])
α = sum((l*ξ).*W̄_interval)

Mᴺ = LinearOperator(pfourier, pfourier, interval.(zeros(1+4*(N+1),1+4*(N+1)))) # Linear operator
component(Mᴺ,1,1)[1,1] = interval(-1)
component(Mᴺ, 1, 4) .= transpose(coefficients(ξ₁.*l₁₁c + ξ₂.*l₂₁c))
component(Mᴺ, 1, 5) .= transpose(coefficients(ξ₁.*l₁₂c + ξ₂.*l₂₂c))

project!(component(Mᴺ,2,1), Derivative(2)*Ū₁_interval)
project!(component(Mᴺ,4,1), Derivative(2)*W̄₁_interval)

project!(component(Mᴺ,2,2), 𝕍₁ᴺ)
project!(component(Mᴺ,2,3), 𝕍₂ᴺ)
project!(component(Mᴺ,3,2), -𝕍₁ᴺ)
project!(component(Mᴺ,3,3), -𝕍₂ᴺ)

project!(component(Mᴺ,4,2), 𝕍₃ᴺ)
project!(component(Mᴺ,4,3), 𝕍₄ᴺ)
project!(component(Mᴺ,5,2), -𝕍₃ᴺ)
project!(component(Mᴺ,5,3), -𝕍₄ᴺ)

project!(component(Mᴺ,4,4), 𝕍₁ᴺ)
project!(component(Mᴺ,4,5), 𝕍₂ᴺ)
project!(component(Mᴺ,5,4), -𝕍₁ᴺ)
project!(component(Mᴺ,5,5), -𝕍₂ᴺ)

B = interval.((inv(I + mid.(Mᴺ) * mid.(L⁻¹))))
B_adjoint = LinearOperator(pfourier,pfourier, coefficients(B)')
################## 𝒴₀ BOUND ######################################################
@info "Computing 𝒴₀"
# Computation of the 𝒴₀ bound, defined in Lemma 5.3.
# Building G₁
tail_G₂ = Ū₁_interval^2*Ū₂_interval + ν₄i*Ū₁_interval^2 + ν₅i*Ū₁_interval*Ū₂_interval
tail_G₄ = V₁_interval*W̄₁_interval + V₂_interval*W̄₂_interval
G₂ = project(tail_G₂, fourier)
G₄ = project(tail_G₄, fourier)
G = Sequence(pfourier, interval.(zeros(1+4*(N+1))))
tail_G = Sequence(ParameterSpace() × CosFourier(3N₀,π/di) × CosFourier(3N₀,π/di) × CosFourier(3N₀,π/di) × CosFourier(3N₀,π/di), interval.(zeros(1 + 4*(3N₀ + 1))))
component(G,1)[1] = interval(0)
project!(component(G, 2), G₂)
project!(component(G, 3), -G₂)
project!(component(G, 4), G₄)
project!(component(G, 5), -G₄)
component(tail_G,1)[1] = interval(0)
project!(component(tail_G, 2), tail_G₂)
project!(component(tail_G, 3), -tail_G₂)
project!(component(tail_G, 4), tail_G₄)
project!(component(tail_G, 5), -tail_G₄)

Fᴺ = Sequence(pfourier, [sum((l*ξ).*W̄_interval) - α ; coefficients(component(project(L_long*X̄_interval+G,pfourier),2:5))])
𝒴₀ = sqrt(ExactReal(2)*di) * sqrt(norm(B*Fᴺ,2)^2 + norm(component(L_long*(X̄_interval - project(X̄_interval,pfourier)) + tail_G - G,2:5), 2)^2)
@show 𝒴₀
################## 𝒵₂ BOUND ######################################################
@info "Computing 𝒵₂"    
# Computation of the 𝒵₂ bound, defined in Lemma 5.4.
Q₃ = ExactReal(2)*W̄₂_interval 
Q₄ = ExactReal(2)*W̄₁_interval
ℚ₁ = project(Multiplication(Q₁), fourier, fourier,Interval{Float64})
ℚ₂ = project(Multiplication(Q₂), fourier, fourier,Interval{Float64})
ℚ₃ = project(Multiplication(Q₃), fourier, fourier,Interval{Float64})
ℚ₄ = project(Multiplication(Q₄), fourier, fourier,Interval{Float64})
ℚ₁² = project(Multiplication(Q₁^2), fourier, fourier,Interval{Float64})
ℚ₂² = project(Multiplication(Q₂^2), fourier, fourier,Interval{Float64})
ℚ₁ℚ₃ = project(Multiplication(Q₁*Q₃), fourier, fourier,Interval{Float64})
ℚ₂ℚ₄ = project(Multiplication(Q₂*Q₄), fourier, fourier,Interval{Float64})
ℚ₃² = project(Multiplication(Q₃^2), fourier, fourier,Interval{Float64})
ℚ₄² = project(Multiplication(Q₄^2), fourier, fourier,Interval{Float64})

M₁ = LinearOperator(fourier × fourier, pfourier, [coefficients(component(B,1,2)-component(B,1,3)) coefficients(component(B,1,4)-component(B,1,5)) ; coefficients(component(B,2,2)-component(B,2,3)) coefficients(component(B,2,4)-component(B,2,5)) ; coefficients(component(B,3,2)-component(B,3,3)) coefficients(component(B,3,4)-component(B,3,5)) ; coefficients(component(B,4,2)-component(B,5,2)) coefficients(component(B,4,4)-component(B,4,5)) ; coefficients(component(B,5,2)-component(B,5,3)) coefficients(component(B,5,4)-component(B,5,5))])
M₁_adjoint = LinearOperator(pfourier, fourier × fourier, coefficients(M₁)')
M₂ = LinearOperator(fourier × fourier, fourier × fourier, [coefficients(ℚ₁² + ℚ₂²) coefficients(ℚ₁ℚ₃ + ℚ₂ℚ₄) ; coefficients(ℚ₁ℚ₃ + ℚ₂ℚ₄) coefficients(ℚ₁² + ℚ₂² + ℚ₃² + ℚ₄²)])
M₂πₙM₂_adjoint = LinearOperator(fourier × fourier, fourier × fourier, [coefficients(ℚ₁² + ℚ₂² - _matprod2(ℚ₁,ℚ₁) - _matprod2(ℚ₂,ℚ₂)) coefficients(ℚ₁ℚ₃ + ℚ₂ℚ₄ - _matprod2(ℚ₁,ℚ₃) - _matprod2(ℚ₂,ℚ₄)) ; coefficients(ℚ₁ℚ₃ + ℚ₂ℚ₄ - _matprod2(ℚ₃,ℚ₁) - _matprod2(ℚ₄,ℚ₂)) coefficients(ℚ₁² + ℚ₂² + ℚ₃² + ℚ₄² - _matprod2(ℚ₁,ℚ₁) - _matprod2(ℚ₂,ℚ₂) - _matprod2(ℚ₃,ℚ₃) - _matprod2(ℚ₄,ℚ₄))])

B₁₅_2_4 = LinearOperator(fourier × fourier, pfourier, [coefficients(component(B,1,2)) coefficients(component(B,1,4)) ; coefficients(component(B,2,2)) coefficients(component(B,2,4)) ; coefficients(component(B,3,2)) coefficients(component(B,3,4)) ; coefficients(component(B,4,2)) coefficients(component(B,4,4)) ; coefficients(component(B,5,2)) coefficients(component(B,5,4))])
B₁₅_2_4_adjoint = LinearOperator(pfourier, fourier × fourier, coefficients(B₁₅_2_4)')
# We create a P operator that allows us to compute the operator norm in CosFourier
P = interval.(sqrt(2)*(vec(ones(N+1, 1))))
P[1,1] = interval(1)
P⁻¹ = (interval.(ones(N+1))./P)

norm_M₁ = sqrt(opnorm(LinearOperator([P ; P].*coefficients(_matprod2(M₁_adjoint,M₁)).*[P⁻¹ ; P⁻¹]'),2))
norm_B₁₅_2_4 = sqrt(opnorm(LinearOperator([P ; P].*coefficients(_matprod2(B₁₅_2_4_adjoint,B₁₅_2_4)).*[P⁻¹ ; P⁻¹]'),2))
# Computing κ
l_den2(ξ) = ν̄_interval*abs(interval(2π)*ξ)^4 + (ν̄_interval*ν₂i - ν₁i)*abs(interval(2π)*ξ)^2 - ν₂i*(ν₁i+ν₃i)
l₁₁2(ξ) = -abs(interval(2π)*ξ)^2*ν̄_interval + ν₁i
l₁₂2(ξ) = ν₂i
l₂₁2(ξ) = ν₃i
l₂₂2(ξ) = -abs(interval(2π)*ξ)^2 - ν₂i

# Computing the bound on ||l⁻¹||_ℳ₁
norm_ℳ₁_𝓁⁻¹_component_1_1 = _compute_ℳ₁_component(ExactReal(-1),-ν₂i,ν̄_interval,ν₁i,ν₂i,ν₃i,l₂₂2,l_den2)
norm_ℳ₁_𝓁⁻¹_component_1_2 = max(abs(ν₂i/l_den2(interval(0))),abs(ν₂i/l_den2(cbrt(interval(8)*interval(π^2)*(ν̄_interval*ν₂i - ν₁i)/(interval(64)*interval(π^4))))))
norm_ℳ₁_𝓁⁻¹_component_2_1 = max(abs(ν₃i/l_den2(interval(0))),abs(ν₃i/l_den2(cbrt(interval(8)*interval(π^2)*(ν̄_interval*ν₂i - ν₁i)/(interval(64)*interval(π^4))))))
norm_ℳ₁_𝓁⁻¹_component_2_2 = _compute_ℳ₁_component(-ν̄_interval,ν₁i,ν̄_interval,ν₁i,ν₂i,ν₃i,l₁₁2,l_den2)
norm_ℳ₁_𝓁⁻¹ = sqrt(norm_ℳ₁_𝓁⁻¹_component_1_1^2 + norm_ℳ₁_𝓁⁻¹_component_1_2^2 + norm_ℳ₁_𝓁⁻¹_component_2_1^2 + norm_ℳ₁_𝓁⁻¹_component_2_2^2)
# Computing the bound on |l⁻¹|ₘ₂
_val_1_squared,_val_2_squared,_val_3_squared,_val_4_squared = integral_computation(νi,ν₁i,ν₂i,ν₃i)
norm_ℳ₂_𝓁⁻¹ = maximum([sqrt(_val_1_squared + _val_2_squared) sqrt(_val_3_squared + _val_4_squared)])

κ = norm_ℳ₁_𝓁⁻¹ * norm_ℳ₂_𝓁⁻¹

𝒵₂₁ = norm_B₁₅_2_4*_𝒵₂₁_ℳ₁_bound(ν̄_interval,ν₁i,ν₂i,ν₃i,l₁₂2,l₂₂2,l_den2)
𝒵₂₂ = norm_M₁*ExactReal(2)*sqrt(interval(10))*κ*norm_ℳ₂_𝓁⁻¹*r₀
𝒵₂₃ = opnorm(LinearOperator([interval(1) ; P ; P ; P ; P].*coefficients(_matprod2(_matprod2(M₁,M₂),M₁_adjoint)).*[interval(1) ; P⁻¹; P⁻¹ ; P⁻¹ ; P⁻¹]'), 2)
𝒵₂₄ = sqrt(opnorm(LinearOperator([interval(1) ; P ; P ; P ; P].*coefficients(_matprod2(_matprod2(M₁,M₂πₙM₂_adjoint),M₁_adjoint)).*[interval(1) ; P⁻¹; P⁻¹ ; P⁻¹ ; P⁻¹]'),2))
𝒵₂₅ = φ(norm(Q₁^2 + Q₂^2, 1),norm(Q₁*Q₃+Q₂*Q₄,1),norm(Q₃*Q₁+Q₄*Q₂,1),norm(Q₁^2 + Q₂^2 + Q₃^2 + Q₄^2,1))

𝒵₂ = (ExactReal(1)+sqrt(interval(3)))*𝒵₂₁ + 𝒵₂₂ + ExactReal(5)*κ*sqrt(φ(𝒵₂₃,𝒵₂₄,𝒵₂₄,𝒵₂₅))
@show 𝒵₂
################## 𝒵₁ BOUND ######################################################
V₁ᴺ_interval = project(V₁_interval,CosFourier(N,π/di))
V₂ᴺ_interval = project(V₂_interval,CosFourier(N,π/di))
V₃ᴺ_interval = project(V₃_interval,CosFourier(N,π/di))
V₄ᴺ_interval = project(V₄_interval,CosFourier(N,π/di))
@info "Computing 𝒵_∞"   
# Computation of 𝒵_∞, defined in Lemma 5.5
l⁻¹_norm = φ(norm_ℳ₁_𝓁⁻¹_component_1_1, norm_ℳ₁_𝓁⁻¹_component_1_2, norm_ℳ₁_𝓁⁻¹_component_2_1, norm_ℳ₁_𝓁⁻¹_component_2_2)
𝒵_∞₁ = interval(0) #As ξ is chosen with N coefficients.
𝒵_∞₂ = ExactReal(2)*di*sqrt(norm(Derivative(2)*(Ū₁_interval - project(Ū₁_interval,fourier)),2)^2 + norm(Derivative(2)*(W̄₁_interval - project(W̄₁_interval,fourier)),2)^2)
𝒵_∞₃ = l⁻¹_norm*φ(sqrt(norm(V₁_interval - V₁ᴺ_interval,1)^2 + sqrt(norm(V₂_interval - V₂ᴺ_interval,1)^2)),0,sqrt(norm(V₃_interval - V₃ᴺ_interval,1)^2 + sqrt(norm(V₄_interval - V₄ᴺ_interval,1)^2)),sqrt(norm(V₁_interval - V₁ᴺ_interval,1)^2 + sqrt(norm(V₂_interval - V₂ᴺ_interval,1)^2)))
𝒵_∞ = φ(interval(0),𝒵_∞₁,𝒵_∞₂,𝒵_∞₃)

@info "Computing Z₁"   
# Computation of Z₁, defined in Lemma 5.6
l₁₁2N = -(interval.(2N+1)*π/di)^2*ν̄_interval + ν₁i
l₁₂2N = ν₂i
l₂₁2N = ν₃i
l₂₂2N = -(interval.(2N+1)*π/di)^2 - ν₂i
l_den2N = l₁₁2N*l₂₂2N - l₁₂2N*l₂₁2N

Z₁₁ = abs(l₂₂2N/l_den2N) * norm(V₁ᴺ_interval,1) + abs(l₂₁2N/l_den2N) * norm(V₂ᴺ_interval,1)
Z₁₂ = abs(l₁₂2N/l_den2N) * norm(V₁ᴺ_interval,1) + abs(l₁₁2N/l_den2N) * norm(V₂ᴺ_interval,1)
Z₁₃ = abs(l₂₂2N/l_den2N) * norm(V₃ᴺ_interval,1) + abs(l₂₁2N/l_den2N) * norm(V₄ᴺ_interval,1)
Z₁₄ = abs(l₁₂2N/l_den2N) * norm(V₃ᴺ_interval,1) + abs(l₁₁2N/l_den2N) * norm(V₄ᴺ_interval,1)

fourier2 = CosFourier(2N,π/di)
fourier3 = CosFourier(3N,π/di)

M_2N_3N_old = LinearOperator(fourier2 × fourier2, fourier3 × fourier3, interval.(zeros(2*(3N+1),2*(2N+1))))
l₁₁_2N_3N = diag(coefficients(project(Derivative(2), fourier2, fourier2,Interval{Float64})*ν̄_interval + UniformScaling(interval(1)) * ν₁i))
l₁₂_2N_3N = interval.(ones(2N+1))*ν₂i
l₂₁_2N_3N = interval.(ones(2N+1))*ν₃i
l₂₂_2N_3N = diag(coefficients(project(Derivative(2), fourier2, fourier2,Interval{Float64}) - UniformScaling(interval(1)) * ν₂i)) 
l_den_2N_3N = l₁₁_2N_3N.*l₂₂_2N_3N - l₂₁_2N_3N.*l₁₂_2N_3N

𝕍₁ᴺ_2N_3N = project(Multiplication(V₁ᴺ_interval),fourier2,fourier3,Interval{Float64})
𝕍₂ᴺ_2N_3N = project(Multiplication(V₂ᴺ_interval),fourier2,fourier3,Interval{Float64})
project!(component(M_2N_3N_old, 1, 1), UniformScaling(interval(1)) + 𝕍₁ᴺ_2N_3N.*(l₂₂_2N_3N./l_den_2N_3N)' - 𝕍₂ᴺ_2N_3N.*(l₂₁_2N_3N./l_den_2N_3N)')
project!(component(M_2N_3N_old, 1, 2), -𝕍₁ᴺ_2N_3N.*(l₁₂_2N_3N./l_den_2N_3N)' + 𝕍₂ᴺ_2N_3N.*(l₁₁_2N_3N./l_den_2N_3N)')
project!(component(M_2N_3N_old, 2, 1), -𝕍₁ᴺ_2N_3N.*(l₂₂_2N_3N./l_den_2N_3N)' + 𝕍₂ᴺ_2N_3N.*(l₂₁_2N_3N./l_den_2N_3N)')
project!(component(M_2N_3N_old, 2, 2), UniformScaling(interval(1)) + 𝕍₁ᴺ_2N_3N.*(l₁₂_2N_3N./l_den_2N_3N)' - 𝕍₂ᴺ_2N_3N.*(l₁₁_2N_3N./l_den_2N_3N)')

M_2N_3N_new = LinearOperator(fourier2 × fourier2, fourier3 × fourier3, interval.(zeros(2*(3N+1),2*(2N+1))))

𝕍₃ᴺ_2N_3N = project(Multiplication(V₃ᴺ_interval),fourier2,fourier3,Interval{Float64})
𝕍₄ᴺ_2N_3N = project(Multiplication(V₄ᴺ_interval),fourier2,fourier3,Interval{Float64})
project!(component(M_2N_3N_new, 1, 1), 𝕍₃ᴺ_2N_3N.*(l₂₂_2N_3N./l_den_2N_3N)' - 𝕍₄ᴺ_2N_3N.*(l₂₁_2N_3N./l_den_2N_3N)')
project!(component(M_2N_3N_new, 1, 2), -𝕍₃ᴺ_2N_3N.*(l₁₂_2N_3N./l_den_2N_3N)' + 𝕍₄ᴺ_2N_3N.*(l₁₁_2N_3N./l_den_2N_3N)')
project!(component(M_2N_3N_new, 2, 1), -𝕍₃ᴺ_2N_3N.*(l₂₂_2N_3N./l_den_2N_3N)' + 𝕍₄ᴺ_2N_3N.*(l₂₁_2N_3N./l_den_2N_3N)')
project!(component(M_2N_3N_new, 2, 2), 𝕍₃ᴺ_2N_3N.*(l₁₂_2N_3N./l_den_2N_3N)' - 𝕍₄ᴺ_2N_3N.*(l₁₁_2N_3N./l_den_2N_3N)')

M_2N_3N = LinearOperator(ParameterSpace() × fourier2 × fourier2 × fourier2 × fourier2,ParameterSpace() × fourier3 × fourier3 × fourier3 × fourier3, interval.(zeros(1 + 4*(3N+1),1 + 4*(2N+1))))
project!(component(M_2N_3N,2:3,2:3), M_2N_3N_old)
project!(component(M_2N_3N,4:5,2:3), M_2N_3N_new)
project!(component(M_2N_3N,4:5,4:5), M_2N_3N_old)

component(M_2N_3N, 1, 4) .= transpose(coefficients(project(ξ₁,fourier2)))
component(M_2N_3N, 1, 5) .= transpose(coefficients(project(ξ₂,fourier2)))

project!(component(M_2N_3N,2,1), component(Mᴺ,2,1))
project!(component(M_2N_3N,4,1), component(Mᴺ,4,1))

B_3N = project(B,ParameterSpace() × fourier3 × fourier3 × fourier3 × fourier3,ParameterSpace() × fourier3 × fourier3 × fourier3 × fourier3)
component(B_3N,2,2)[N+1:end,N+1:end] .= Diagonal(interval.(ones(2N)))
component(B_3N,3,3)[N+1:end,N+1:end] .= Diagonal(interval.(ones(2N)))
component(B_3N,4,4)[N+1:end,N+1:end] .= Diagonal(interval.(ones(2N)))
component(B_3N,5,5)[N+1:end,N+1:end] .= Diagonal(interval.(ones(2N)))

P_2N = interval.(sqrt(2)*(vec(ones(2N+1, 1))))
P_2N[1,1] = interval(1)
P_2N⁻¹ = (interval.(ones(2N+1))./P_2N)
P_3N = interval.(sqrt(2)*(vec(ones(3N+1, 1))))
P_3N[1,1] = interval(1)

Z₀ = opnorm(LinearOperator(coefficients([interval(1) ; P_3N ; P_3N ; P_3N ; P_3N].*(UniformScaling(interval(1)) - _matprod2(B_3N,M_2N_3N)).*[interval(1) ; P_2N⁻¹ ; P_2N⁻¹ ; P_2N⁻¹ ; P_2N⁻¹]')),2)

Z₁ = sqrt(Z₀^2 + ExactReal(2)*(sqrt(Z₁₁^2 + Z₁₂^2) + sqrt(Z₁₃^2 + Z₁₄^2))^2)
@show Z₁

@info "Computing 𝒵ᵤ"   
# Computation of 𝒵ᵤ, defined in Lemma 5.8
P_full = [P ; P ; P ; P]
P⁻¹_full = [P⁻¹ ; P⁻¹ ; P⁻¹ ; P⁻¹]

# Computing the constants Cⱼ and a defined in Lemma 4.6.
a,C₁,C₂,C₃,C₄ = _compute_C_a(ν̄_interval,ν₁i,ν₂i,ν₃i)

# Building the Fourier series of E.
E = Sequence(CosFourier(2N,π/d), interval.(zeros(2N+1)))
for n = 0:2N
    E[n] = ExactReal(2)*a* (interval(-1))^interval(n)/(ExactReal(4)*a^2 + (interval(n*π)/di)^2)
end

Cd = ExactReal(4)*di + ExactReal(4)*exp(-a*di)/(a*(ExactReal(1)-exp(-interval(3/2)*a*di))) + ExactReal(2)/(a*(ExactReal(1)-exp(-ExactReal(2)*a*di)))

# Computing the inner products.
EV₁ᴺ = _conv_small(E,V₁ᴺ_interval,N)
EV₂ᴺ = _conv_small(E,V₂ᴺ_interval,N)
V₁ᴺ_inner_prodEV₁ᴺ = abs(coefficients(P.*V₁ᴺ_interval)'*coefficients(P.*EV₁ᴺ))
V₂ᴺ_inner_prodEV₂ᴺ = abs(coefficients(P.*V₂ᴺ_interval)'*coefficients(P.*EV₂ᴺ))

𝒵ᵤ₁₁ = sqrt(C₁^2*(ExactReal(1)-exp(-ExactReal(4)*a*di))/a * V₁ᴺ_inner_prodEV₁ᴺ)
𝒵ᵤ₁₂ = sqrt(C₂^2*(ExactReal(1)-exp(-ExactReal(4)*a*di))/a * V₂ᴺ_inner_prodEV₂ᴺ)
𝒵ᵤ₁₃ = sqrt(C₃^2*(ExactReal(1)-exp(-ExactReal(4)*a*di))/a * V₁ᴺ_inner_prodEV₁ᴺ)
𝒵ᵤ₁₄ = sqrt(C₄^2*(ExactReal(1)-exp(-ExactReal(4)*a*di))/a * V₂ᴺ_inner_prodEV₂ᴺ)
𝒵ᵤ₁ = sqrt((𝒵ᵤ₁₁ + 𝒵ᵤ₁₂)^2 + (𝒵ᵤ₁₃ + 𝒵ᵤ₁₄)^2)

𝒵ᵤ₂₁ = sqrt(𝒵ᵤ₁₁^2 + Cd*C₁^2*(exp(-ExactReal(2)*a*di)-exp(-ExactReal(6)*a*di))*V₁ᴺ_inner_prodEV₁ᴺ)
𝒵ᵤ₂₂ = sqrt(𝒵ᵤ₁₂^2 + Cd*C₂^2*(exp(-ExactReal(2)*a*di)-exp(-ExactReal(6)*a*di))*V₂ᴺ_inner_prodEV₂ᴺ)
𝒵ᵤ₂₃ = sqrt(𝒵ᵤ₁₃^2 + Cd*C₃^2*(exp(-ExactReal(2)*a*di)-exp(-ExactReal(6)*a*di))*V₁ᴺ_inner_prodEV₁ᴺ)
𝒵ᵤ₂₄ = sqrt(𝒵ᵤ₁₄^2 + Cd*C₄^2*(exp(-ExactReal(2)*a*di)-exp(-ExactReal(6)*a*di))*V₂ᴺ_inner_prodEV₂ᴺ)
𝒵ᵤ₂ = sqrt((𝒵ᵤ₂₁ + 𝒵ᵤ₂₂)^2 + (𝒵ᵤ₂₃ + 𝒵ᵤ₂₄)^2)
𝒵ᵤ₂ = sqrt((𝒵ᵤ₂₁ + 𝒵ᵤ₂₂)^2 + (𝒵ᵤ₂₃ + 𝒵ᵤ₂₄)^2)

EV₃ᴺ = _conv_small(E,V₃ᴺ_interval,N)
EV₄ᴺ = _conv_small(E,V₄ᴺ_interval,N)
V₃ᴺ_inner_prodEV₃ᴺ = abs(coefficients(P.*V₃ᴺ_interval)'*coefficients(P.*EV₃ᴺ))
V₄ᴺ_inner_prodEV₄ᴺ = abs(coefficients(P.*V₄ᴺ_interval)'*coefficients(P.*EV₄ᴺ))

𝒵ᵤ₃₁ = sqrt(C₁^2*(ExactReal(1)-exp(-ExactReal(4)*a*di))/a * V₃ᴺ_inner_prodEV₃ᴺ)
𝒵ᵤ₃₂ = sqrt(C₂^2*(ExactReal(1)-exp(-ExactReal(4)*a*di))/a * V₄ᴺ_inner_prodEV₄ᴺ)
𝒵ᵤ₃₃ = sqrt(C₃^2*(ExactReal(1)-exp(-ExactReal(4)*a*di))/a * V₃ᴺ_inner_prodEV₃ᴺ)
𝒵ᵤ₃₄ = sqrt(C₄^2*(ExactReal(1)-exp(-ExactReal(4)*a*di))/a * V₄ᴺ_inner_prodEV₄ᴺ)
𝒵ᵤ₃ = sqrt((𝒵ᵤ₃₁ + 𝒵ᵤ₃₂)^2 + (𝒵ᵤ₃₃ + 𝒵ᵤ₃₄)^2)

𝒵ᵤ₄₁ = sqrt(𝒵ᵤ₃₁^2 + Cd*C₁^2*(exp(-ExactReal(2)*a*di)-exp(-ExactReal(6)*a*di))*V₃ᴺ_inner_prodEV₃ᴺ)
𝒵ᵤ₄₂ = sqrt(𝒵ᵤ₃₂^2 + Cd*C₂^2*(exp(-ExactReal(2)*a*di)-exp(-ExactReal(6)*a*di))*V₄ᴺ_inner_prodEV₄ᴺ)
𝒵ᵤ₄₃ = sqrt(𝒵ᵤ₃₃^2 + Cd*C₃^2*(exp(-ExactReal(2)*a*di)-exp(-ExactReal(6)*a*di))*V₃ᴺ_inner_prodEV₃ᴺ)
𝒵ᵤ₄₄ = sqrt(𝒵ᵤ₃₄^2 + Cd*C₄^2*(exp(-ExactReal(2)*a*di)-exp(-ExactReal(6)*a*di))*V₄ᴺ_inner_prodEV₄ᴺ)
𝒵ᵤ₄ = sqrt((𝒵ᵤ₄₁ + 𝒵ᵤ₄₂)^2 + (𝒵ᵤ₄₃ + 𝒵ᵤ₄₄)^2)

𝒵ᵤ = norm_M₁*sqrt(interval(2))*(sqrt(𝒵ᵤ₁^2 + 𝒵ᵤ₂^2) + sqrt(𝒵ᵤ₃^2 + 𝒵ᵤ₄^2))

𝒵₁ = Z₁ + 𝒵ᵤ + norm_M₁*𝒵_∞

################## Computer Assisted Proof ######################################################
𝒴₀ = interval(sup(𝒴₀))
𝒵₁ = interval(sup(𝒵₁))
𝒵₂ = interval(sup(𝒵₂))
r_min = sup((interval(1) - 𝒵₁ - sqrt((interval(1) - 𝒵₁)^2 - interval(2)*𝒴₀*𝒵₂))/𝒵₂)
r_max = inf((interval(1) - 𝒵₁ + sqrt((interval(1) - 𝒵₁)^2 - interval(2)*𝒴₀*𝒵₂))/𝒵₂)
CAP(sup(𝒴₀),sup(𝒵₁),sup(𝒵₂))


r0 = r_min # radius of the ball in which the proof is done




############## Stability analysis ######################################################
# Proves the result of Thoerem 6.6 ensuring we have a saddle node bifurcation.
@info "Starting the enclosure of the spectrum"

    t = - interval(1) # precomputed shift for the spectrum to the left half-plane. This is done by computing the Gershgorin disks a first time with a rough shift (given in Lemma 6.3). Then we notice that t = -1 is a good shift for all the examples treated in the paper.

    l11 = diag(coefficients(project(Derivative(2), fourier, fourier,Interval{Float64})*νi + UniformScaling(interval(1)) * ν₁i))
    l12 = interval.(ones(N+1))*ν₂i
    l21 = interval.(ones(N+1))*ν₃i
    l22 = diag(coefficients(project(Derivative(2), fourier, fourier,Interval{Float64}) - UniformScaling(interval(1)) * ν₂i))
    l_den = l11.*l22 - l21.*l12
    
    L = LinearOperator(fourier^2, fourier^2, interval.(zeros(2*(N+1),2*(N+1))))
    component(L, 1, 1) .= Diagonal(l11)
    component(L, 1, 2) .= Diagonal(l12)
    component(L, 2, 1) .= Diagonal(l21)
    component(L, 2, 2) .= Diagonal(l22)


    # Computation of DF
    
    V₁_interval = ExactReal(2)*Ū₁_interval*Ū₂_interval + ExactReal(2)*ν₄i*Ū₁_interval + ν₅i*Ū₂_interval
    V₂_interval = Ū₁_interval^2 + ν₅i*Ū₁_interval
    Dg₁₁ = project(Multiplication(V₁_interval) ,fourier, fourier, Interval{Float64})
    Dg₁₂ = project(Multiplication(V₂_interval) ,fourier, fourier, Interval{Float64})

    DF = LinearOperator(fourier^2, fourier^2, interval.(zeros(2*(N+1),2*(N+1))))
    component(DF, 1, 1) .=  coefficients(Dg₁₁)
    component(DF, 1, 2) .=  coefficients(Dg₁₂)
    component(DF, 2, 1) .=  -coefficients(Dg₁₁)
    component(DF, 2, 2) .=  -coefficients(Dg₁₂)

    D1 = sqrt(interval(2))*interval.(ones(2*(N+1))) ; D2 = interval.(ones(2*(N+1)))*sqrt(interval(0.5))
    D1[1] = interval(1); D1[N+2] = interval(1) ; D2[1] = interval(1); D2[N+2] = interval(1) 

    DF = DF + L

    D,P =  eigen(-mid.(D1).*coefficients(mid.(DF)).*mid.(D2)')

    P = interval.(mid.(D2).*P.*mid.(D1)') ; Pinv = interval.(inv(mid.(P))) ; nP = opnorm(LinearOperator(I - D1.*_cmatprod(Pinv,P).*D2'),2)
    norm_P = spec_norm(D1.*P.*D2') ; norm_Pinv = spec_norm(D1.*Pinv.*D2')  

    # display("norm of Pinv")
    # display(norm_Pinv)

    D = _cmatprod(_cmatprod(Pinv,coefficients(DF)),P)  ; DF = Nothing
    S = diag(D) ; R = D
    for i ∈ 1:2*(N+1)
        R[i,i] = interval(0)
    end 

    St = S .+ t ;  Stinv = ExactReal(1) ./ St 
    V1 = V₁_interval
    V2 = V₂_interval

    ### computation of \|π_N (L-δ0)^{-1}\|_2. For this we compute the eigenvalues of l^{-1}(ξ) and evaluate the maximum for ξ \geq (N+1)π/d 
    lden = (ν₁ - ν*(interval(N+1)*π/di)^2)*( -ν₂ - (interval(N+1)*π/di)^2) - ν₃*ν₂
    a1 = ( -ν₂ - (interval(N+1)*π/di)^2 + V1[0])/lden
    a2 = (-ν₂ + V2[0])/lden
    a3 = (-ν₃-V1[0])/lden
    a4 = (ν₁ - ν*(interval(N+1)*π/di)^2 - V2[0])/lden 

    ### formula for the eigenvalues of a matrix [a1 a2;a3 a4]
    max_Linv = abs(ExactReal(0.5)*(a1 + a4 + sqrt(interval(4)*a2*a3 + (a1-a4)^2))) 

    Z12 = max_Linv*sqrt(interval(2)*norm(V1-V1[0],1)^2 + interval(2)*norm(V2-V2[0],1)^2)
    # display("Z12")
    # display(Z12)

    Z13 = spec_norm((D1.*Stinv).*R.*D2')*(ExactReal(1)+ nP*norm_Pinv/(ExactReal(1)-nP))
    # display("Z13")
    # display(Z13)

    DF = LinearOperator(CosFourier(3N,π/di)^2, fourier^2, interval.(zeros(2*(N+1),2*(3N+1))))
    Dg₁₁ = project(Multiplication(V₁_interval) ,CosFourier(3N,π/di) , fourier, Interval{Float64})
    Dg₁₂ = project(Multiplication(V₂_interval) ,CosFourier(3N,π/di) , fourier, Interval{Float64})
    component(DF, 1, 1) .=  coefficients(Dg₁₁)
    component(DF, 1, 2) .=  coefficients(Dg₁₂)
    component(DF, 2, 1) .=  -coefficients(Dg₁₁)
    component(DF, 2, 2) .=  -coefficients(Dg₁₂)
    DF = coefficients(DF)  ; DF = DF[:,[N+2:3*N+1 ; 4N+3:6N+2]]
    DF = Stinv.*DF
    

    Z14 = sqrt(interval(0.5))*spec_norm(D1.*Matrix(DF))*(ExactReal(1)+ nP*norm_Pinv/(ExactReal(1)-nP))
    # display("Z14")
    # display(Z14)


    DF = LinearOperator(fourier^2, fourier^2, interval.(zeros(2*(N+1),2*(N+1))))
    Dg₁₁ = project(Multiplication(V1^2 + V2^2) , fourier , fourier, Interval{Float64})
    
    component(DF, 1, 1) .=  coefficients(Dg₁₁)
    component(DF, 1, 2) .=  -coefficients(Dg₁₁)
    component(DF, 2, 1) .=  -coefficients(Dg₁₁)
    component(DF, 2, 2) .=  coefficients(Dg₁₁)
    Z11 = max_Linv*sqrt(spec_norm(D1.*_cmatprod(_cmatprod(Matrix(P'),coefficients(DF)),P).*D2'))
    # display("Z11")
    # display(Z11)


    
    ###### Computation of the bounds 𝒞1*r0 an 𝒞2*r0

    norm_SPL = spec_norm((D1.*Stinv).*Pinv.*D2')*(ExactReal(1)+ nP*norm_Pinv/(ExactReal(1)-nP))

    # display("value norm SPL")
    # display(norm_SPL)

    # ##### computation of an upper bound for \|(L-mu)^{-1}\|_2 
    # Linv = interval(inv(mid.(L))) ; up_Linv = spec_norm(coefficients(Linv))*(interval(1) + spec_norm(I - coefficients(Linv*L)))
    

    Q₁ = ExactReal(2)*Ū₂_interval + ExactReal(2)*ν₄i
    Q₂ = ExactReal(2)*Ū₁_interval + ν₅i
    𝒵₂₃ = norm(Q₁^2 + Q₂^2, 1) ; 𝒵23 = sqrt(𝒵₂₃) ; 

    𝒞1 = norm_ℳ₁_𝓁⁻¹*(sqrt(interval(5))*κ*𝒵23 + interval(3)*norm_ℳ₂_𝓁⁻¹*r0)*r0
    𝒞2 = norm_SPL*(sqrt(interval(5))*κ*𝒵23 + interval(3)*norm_ℳ₂_𝓁⁻¹*r0)*r0

    # display("values of the 𝒞i")
    # display(𝒞1)
    # display(𝒞2)

    ########## Computation of the bound 𝒵u3

    𝒵u1 = 𝒵ᵤ₁
    𝒵u2 = 𝒵ᵤ₂
    𝒵u3 = norm_SPL*𝒵u2

    # display("value of 𝒵u3")
    # display(𝒵u3)

    ######### Computation of ϵ


    if sup(𝒞1)<1
        κ1 = (𝒵u1 + 𝒞1)/(ExactReal(1)-𝒞1)
        # display("κ1")
        # display(κ1)
        if sup(Z12 + 𝒵u2 + sqrt(ExactReal(1) + κ1^2)*𝒞1) < 1
            if sup(Z12 + 𝒵u2) < 1
                κ2 = (Z11 + (𝒵u2 + sqrt(ExactReal(1) + κ1^2)*𝒞1)*norm_P)/(ExactReal(1) - (Z12 + 𝒵u2 + sqrt(ExactReal(1) + κ1^2)*𝒞1))
                # display("κ2")
                # display(κ2)
                ϵq = Z13 + Z14*(Z11 + ExactReal(2)*𝒵u2*norm_P)/(ExactReal(1) - Z12 - ExactReal(2)*𝒵u2) + ExactReal(2)*𝒵u3*(norm_P + (Z11 + ExactReal(2)*𝒵u2*norm_P)/(ExactReal(1) - Z12 - ExactReal(2)*𝒵u2))
                ϵ = Z13 + Z14*κ2 + (𝒵u3 + 𝒞2*sqrt(ExactReal(1) + κ1^2))*(norm_P + κ2)
                return maximum([ϵ ϵq]),S
            else 
                display("third condition not respected")
                return Nan
            end
        else 
            display("second condition not respected")
            return Nan 
        end 
    else 
        display("first condition not respected")
        return Nan 
    end 


    ###### Counting the number of eigenvalues with positive real part
    k = 1
    nDF = 0 # number of eigenvalues of DF with positive real part
    while inf(real(S[k])) > 0
        global k, nDF
        k += 1
        nDF += 1
    end

    ##### now we verify that the rest of the disks is disjoint from the disks associated with eigenvalues with postitive real part
    for j = 1:k-1
        for n = k:length(S)
            if sup(abs(S[j]-S[n])) <= inf(ϵ*abs(t+S[j]) + ϵ*abs(t+S[n]))
                display("The disks are not disjoint, proof of stability is inconclusive")
                return Nan
            end
        end
    end

    display("Number of eigenvalues of DF with striclty positive real part: $nDF")

    ###### now we verify that there is no eigenvalue on the imaginary axis for the proof of the saddle-node

    nDF = 0 
    for j = 1:length(S)
        global nDF
        if sup(abs(real(S[j]))) < inf(ϵ*abs(t+S[j]))
            nDF += 1
        end
    end

    if nDF == 1 
         display("There is no eigenvalue on the imaginary axis, there exists a saddle-node !")
        #### we know that 0 is a simple eigenvalue, so we know that nDF will be at least 1
        
    else
       display("There is an eigenvalue on the imaginary axis, proof of saddle-node is inconclusive")
            return Nan
    end