# Computer assisted proof of solutions for the 1D Gylcolsis, Brusselator, Root-Hair, Selkov-Schnakenberg, and Schnakenberg models.
# These are models falling within a general class of Activiator-Inhibitor models of the form 
# ∂ₜu = δ² Δu - cu + dv + u²v + a 
# ∂ₜv = Δv + hu - jv - u²v + b 
# (u,v) = (u(x,t),v(x,t))
# The following code computes the solution and rigorously proves Theorems 4.9, 4.10, 4.11, 4.12, 4.13, 4.14, 6.7, and 6.8 in Sections 4.2 and 6.3 of
# "Proving the existence of localized patterns and saddle node bifurcations in 1D activiator-inhibitor type models"  D. Blanco, M. Cadiot, and D. Fassler

#####################################################################################################################################################################

# Needed packages
using RadiiPolynomial, LinearAlgebra, JLD2
include("matproducts.jl")

#####################################################################################################################################################################


#################################### List of the needed functions : go directly to line 186 for the main code ################################################# 

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

# Checks the conditions of the Radii-Polynomial Theorem (see Section 3.1).
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
#Glycolsis
UV = load("UV_Glycolsis","UV")
N₀ = 1400
N = 1100
# Parameters
δ = 0.045 ; δi = interval(δ)    
c = 1 ; ci = interval(c)
b = 0.44
d = 0.4
j = d
a = 0
h = 0 ; hi = interval(h)
r₀ = interval(2e-7) # value of r₀ for 𝒵₂
#=Brusselator
UV = load("UV_Brusselator","UV")
N₀ = 3200
N = 1750
# Parameters
δ = 0.05 ; δi = interval(δ)    
c = 1.51 ; ci = interval(c)
b = 0
d = 0
j = d
a = 0.3
h = c-1 ; hi = interval(h)
r₀ = interval(8e-5) # value of r₀ for 𝒵₂=#
#=Brusselator Multipulse
UV = load("UV_Brusselator_Multipulse","UV")
N₀ = 2000
N = 1300
# Parameters
δ = 0.0095742405424 ; δi = interval(δ)    
c = 2.3299999237 ; ci = interval(c)
b = 0
d = 0
j = d
a = 16.421100616
h = c-1 ; hi = interval(h)
r₀ = interval(9e-11) # value of r₀ for 𝒵₂=#
#=Root-Hair
UV = load("UV_RootHair","UV")
N₀ = 300
N = 200
# Parameters
δ = 0.01 ; δi = interval(δ)    
c = 2 ; ci = interval(c)
b = 1.8
d = 3.5
j = d
a = 0
h = 1 ; hi = interval(h)
r₀ = interval(6e-7) # value of r₀ for 𝒵₂=#
#=Schnakenberg
UV = load("UV_Schnakenberg","UV")
N₀ = 1300
N = 850
# Parameters
δ = 0.011 ; δi = interval(δ)    
c = 1 ; ci = interval(c)
b = 3.6
d = 0
j = d
a = 2.8
h = 0 ; hi = interval(h)
r₀ = interval(3e-10) # value of r₀ for 𝒵₂=#
#=Selkov-Schnakenberg
UV = load("UV_SelkovSchnakenberg","UV")
N₀ = 4000
N = 3300
# Parameters
δ = 0.01 ; δi = interval(δ) 
c = 1 ; ci = interval(c) 
b = 0.589818
d = 0.005
j = d
a = 1.095
h = 0 ; hi = interval(h)
r₀ = interval(6e-10) # value of r₀ for 𝒵₂=#

λ₁ = (a+b)/(c-h)
λ₂ = (c*λ₁ - a)/(λ₁^2 + d)

ν = δ^2 ; νi = interval(ν)
ν₁ = 2λ₁*λ₂ - c ; ν₁i = interval(ν₁)
ν₂ = d + λ₁^2 ; ν₂i = interval(ν₂)
ν₃ = h - 2λ₁*λ₂ ; ν₃i = interval(ν₃)
ν₄ = λ₂; ν₄i = interval(ν₄)
ν₅ = 2λ₁ ; ν₅i = interval(ν₅)

U = component(UV, 1)
V = component(UV, 2)

# Change of variables
U₁ = U - λ₁
U₂ = V - λ₂
d = π / (frequency(U)) ; di = interval(d) # Domain size
fouriero = CosFourier(N,π/d) 
fourier = CosFourier(N, π/di) # Fourier basis
fourier0 = CosFourier(N₀,π/di)
𝒫 = LinearOperator(fourier0,fourier0,interval.(trace2(N₀)))

# Computing the trace discussed in Section 3.2.
Ū₁_interval = Sequence(fourier0, coefficients(𝒫)*interval.(coefficients(U₁)))
Ū₂_interval = Sequence(fourier0, coefficients(𝒫)*interval.(coefficients(U₂)))
Ū_interval = Sequence(fourier0^2, [Ū₁_interval[:] ; Ū₂_interval[:]])

# Building the Linear Operator l defined in Section 1.2.
@info "Building the Linear Operator"
l₁₁ = diag(coefficients(project(Derivative(2), fourier, fourier,Interval{Float64})*νi + UniformScaling(interval(1)) * ν₁i))
l₁₂ = interval.(ones(N+1))*ν₂i
l₂₁ = interval.(ones(N+1))*ν₃i
l₂₂ = diag(coefficients(project(Derivative(2), fourier, fourier,Interval{Float64}) - UniformScaling(interval(1)) * ν₂i))
l_den = l₁₁.*l₂₂ - l₂₁.*l₁₂

# Computation of B defined in Section 3.3.
@info "Building the B operator"
V₁_interval = ExactReal(2)*Ū₁_interval*Ū₂_interval + ExactReal(2)*ν₄i*Ū₁_interval + ν₅i*Ū₂_interval
V₂_interval = Ū₁_interval^2 + ν₅i*Ū₁_interval
Dg₁₁ = project(Multiplication(V₁_interval) ,fourier, fourier, Interval{Float64})
Dg₁₂ = project(Multiplication(V₂_interval) ,fourier, fourier, Interval{Float64})

M = LinearOperator(fourier^2, fourier^2, interval.(zeros(2*(N+1),2*(N+1))))
project!(component(M, 1, 1), UniformScaling(interval(1)) + Dg₁₁.*(l₂₂./l_den)' - Dg₁₂.*(l₂₁./l_den)')
project!(component(M, 1, 2), -Dg₁₁.*(l₁₂./l_den)' + Dg₁₂.*(l₁₁./l_den)')
project!(component(M, 2, 1), -Dg₁₁.*(l₂₂./l_den)' + Dg₁₂.*(l₂₁./l_den)')
project!(component(M, 2, 2), UniformScaling(interval(1)) + Dg₁₁.*(l₁₂./l_den)' - Dg₁₂.*(l₁₁./l_den)')

B = interval.(inv(mid.(M)))

################## 𝒴₀ BOUND ######################################################
@info "Computing 𝒴₀"
# Computation of the 𝒴₀ bound, defined in Lemma 4.2.
# Building G₁
tail_G₁ = Ū₁_interval^2*Ū₂_interval + ν₄i*Ū₁_interval^2 + ν₅i*Ū₁_interval*Ū₂_interval
G₁ = project(tail_G₁, fourier)
G = Sequence(fourier^2, interval.(zeros(2*(N+1))))
project!(component(G, 1), G₁)
project!(component(G, 2), -G₁)
tail_G = Sequence(CosFourier(3N₀,π/di)^2, interval.(zeros(2*(3N₀+1))))
project!(component(tail_G,1), tail_G₁)
project!(component(tail_G,2), -tail_G₁)

lŪ = Sequence(fourier^2, interval.(zeros(2*(N+1))))
project!(component(lŪ, 1), Derivative(2)*Ū₁_interval*νi + ν₁i*Ū₁_interval + ν₂i*Ū₂_interval)
project!(component(lŪ, 2), ν₃i*Ū₁_interval + Derivative(2)*Ū₂_interval - ν₂i*Ū₂_interval)
Ū₁ᴺ_interval = project(Ū₁_interval,fourier)
Ū₂ᴺ_interval = project(Ū₂_interval,fourier)
lŪ_minus_Ūᴺ = Sequence(fourier0^2, interval.(zeros(2*(N₀+1))))
project!(component(lŪ_minus_Ūᴺ, 1), Derivative(2)*(Ū₁_interval-Ū₁ᴺ_interval)*νi + ν₁i*(Ū₁_interval-Ū₁ᴺ_interval) + ν₂i*(Ū₂_interval-Ū₂ᴺ_interval))
project!(component(lŪ_minus_Ūᴺ, 2), ν₃i*(Ū₁_interval-Ū₁ᴺ_interval) + Derivative(2)*(Ū₂_interval-Ū₂ᴺ_interval) - ν₂i*(Ū₂_interval-Ū₂ᴺ_interval))
𝒴₀ = sqrt(ExactReal(2)*di) * sqrt(norm(B*(lŪ + G),2)^2 + norm(lŪ_minus_Ūᴺ + tail_G - G, 2)^2)
@show 𝒴₀

################## 𝒵₂ BOUND ######################################################
@info "Computing 𝒵₂"    
# Computation of the 𝒵₂ bound, defined in Lemma 4.3.
Q₁ = ExactReal(2)*Ū₂_interval + ExactReal(2)*ν₄i
Q₂ = ExactReal(2)*Ū₁_interval + ν₅i
Q₁² = Q₁*Q₁
Q₂² = Q₂*Q₂
ℚ₁ = project(Multiplication(Q₁), fourier, fourier)
ℚ₂ = project(Multiplication(Q₂), fourier, fourier)
ℚ₁² = project(Multiplication(Q₁²), fourier, fourier)
ℚ₂² = project(Multiplication(Q₂²), fourier, fourier)
B₁₁ = component(B, 1, 1)
B₁₂ = component(B, 1, 2)
B₂₁ = component(B, 2, 1)
B₂₂ = component(B, 2, 2)
BM = LinearOperator(fourier, fourier^2, [coefficients(B₁₁ - B₁₂) ; coefficients(B₂₁ - B₂₂)])
BM_adjoint = LinearOperator(fourier^2, fourier, coefficients(BM)')

# We create a P operator that allows us to compute the operator norm in CosFourier
P = interval.(sqrt(2)*(vec(ones(N+1, 1))))
P[1,1] = interval(1)
P⁻¹ = (interval.(ones(N+1))./P)

norm_BM = sqrt(opnorm(LinearOperator(coefficients(P.*_matprod2(BM_adjoint,BM).*P⁻¹')), 2))

# Computing κ
l_den2(ξ) = νi*abs(interval(2π)*ξ)^4 + (νi*ν₂i - ν₁i)*abs(interval(2π)*ξ)^2 - ν₂i*(ν₁i+ν₃i)
l₁₁2(ξ) = -abs(interval(2π)*ξ)^2*νi + ν₁i
l₁₂2(ξ) = ν₂i
l₂₁2(ξ) = ν₃i
l₂₂2(ξ) = -abs(interval(2π)*ξ)^2 - ν₂i

# Computing the bound on ||l⁻¹||_ℳ₁
norm_ℳ₁_𝓁⁻¹_component_1_1 = _compute_ℳ₁_component(ExactReal(-1),-ν₂i,νi,ν₁i,ν₂i,ν₃i,l₂₂2,l_den2)
norm_ℳ₁_𝓁⁻¹_component_1_2 = max(abs(ν₂i/l_den2(interval(0))),abs(ν₂i/l_den2(cbrt(interval(8)*interval(π^2)*(νi*ν₂i - ν₁i)/(interval(64)*interval(π^4))))))
norm_ℳ₁_𝓁⁻¹_component_2_1 = max(abs(ν₃i/l_den2(interval(0))),abs(ν₃i/l_den2(cbrt(interval(8)*interval(π^2)*(νi*ν₂i - ν₁i)/(interval(64)*interval(π^4))))))
norm_ℳ₁_𝓁⁻¹_component_2_2 = _compute_ℳ₁_component(-νi,ν₁i,νi,ν₁i,ν₂i,ν₃i,l₁₁2,l_den2)
norm_ℳ₁_𝓁⁻¹ = sqrt(norm_ℳ₁_𝓁⁻¹_component_1_1^2 + norm_ℳ₁_𝓁⁻¹_component_1_2^2 + norm_ℳ₁_𝓁⁻¹_component_2_1^2 + norm_ℳ₁_𝓁⁻¹_component_2_2^2)
# Computing the bound on |l⁻¹|ₘ₂
_val_1_squared,_val_2_squared,_val_3_squared,_val_4_squared = integral_computation(νi,ν₁i,ν₂i,ν₃i)
norm_ℳ₂_𝓁⁻¹ = maximum([sqrt(_val_1_squared + _val_2_squared) sqrt(_val_3_squared + _val_4_squared)])

κ = norm_ℳ₁_𝓁⁻¹ * norm_ℳ₂_𝓁⁻¹

𝒵₂₁ = opnorm(LinearOperator([P ; P].*coefficients(_matprod2(_matprod2(BM,(ℚ₁² + ℚ₂²)),BM_adjoint)).*[P⁻¹ ; P⁻¹]'), 2)
𝒵₂₂ = sqrt(opnorm(LinearOperator([P ; P].*coefficients(_matprod2(_matprod2(BM,(ℚ₁² + ℚ₂²) - (_matprod2(ℚ₁,ℚ₁) + _matprod2(ℚ₂,ℚ₂))),BM_adjoint)).*[P⁻¹ ; P⁻¹]'),2))
𝒵₂₃ = norm(Q₁² + Q₂², 1)

𝒵₂ = sqrt(φ(𝒵₂₁, 𝒵₂₂, 𝒵₂₂, 𝒵₂₃))*sqrt(interval(5))*κ + norm_BM*ExactReal(3)*κ*norm_ℳ₂_𝓁⁻¹*r₀
@show 𝒵₂
################## 𝒵₁ BOUND ######################################################
@info "Computing Z₁"   
# Computation of Z₁, defined in Lemma 4.5
V₁ᴺ_interval = project(V₁_interval,CosFourier(N,π/di))
V₂ᴺ_interval = project(V₂_interval,CosFourier(N,π/di))

l₁₁2N = -(interval.(2N+1)*π/di)^2*νi + ν₁i
l₁₂2N = ν₂i
l₂₁2N = ν₃i
l₂₂2N = -(interval.(2N+1)*π/di)^2 - ν₂i
l_den2N = l₁₁2N*l₂₂2N - l₁₂2N*l₂₁2N

Z₁₁ = abs(l₂₂2N/l_den2N) * norm(V₁ᴺ_interval,1) + abs(l₂₁2N/l_den2N) * norm(V₂ᴺ_interval,1)
Z₁₂ = abs(l₁₂2N/l_den2N) * norm(V₁ᴺ_interval,1) + abs(l₁₁2N/l_den2N) * norm(V₂ᴺ_interval,1)

fourier2 = CosFourier(2N,π/di)
fourier3 = CosFourier(3N,π/di)

M_2N_3N = LinearOperator(fourier2^2, fourier3^2, interval.(zeros(2*(3N+1),2*(2N+1))))
l₁₁_2N = diag(coefficients(project(Derivative(2), fourier2, fourier2,Interval{Float64})*νi + UniformScaling(interval(1)) * ν₁i))
l₁₂_2N = interval.(ones(2N+1))*ν₂i
l₂₁_2N = interval.(ones(2N+1))*ν₃i
l₂₂_2N = diag(coefficients(project(Derivative(2), fourier2, fourier2,Interval{Float64}) - UniformScaling(interval(1)) * ν₂i)) 
l_den_2N = l₁₁_2N.*l₂₂_2N - l₂₁_2N.*l₁₂_2N

𝕍₁ᴺ_2N_3N = project(Multiplication(V₁ᴺ_interval),fourier2,fourier3,Interval{Float64})
𝕍₂ᴺ_2N_3N = project(Multiplication(V₂ᴺ_interval),fourier2,fourier3,Interval{Float64})
project!(component(M_2N_3N, 1, 1), UniformScaling(interval(1)) + 𝕍₁ᴺ_2N_3N.*(l₂₂_2N./l_den_2N)' - 𝕍₂ᴺ_2N_3N.*(l₂₁_2N./l_den_2N)')
project!(component(M_2N_3N, 1, 2), -𝕍₁ᴺ_2N_3N.*(l₁₂_2N./l_den_2N)' + 𝕍₂ᴺ_2N_3N.*(l₁₁_2N./l_den_2N)')
project!(component(M_2N_3N, 2, 1), -𝕍₁ᴺ_2N_3N.*(l₂₂_2N./l_den_2N)' + 𝕍₂ᴺ_2N_3N.*(l₂₁_2N./l_den_2N)')
project!(component(M_2N_3N, 2, 2), UniformScaling(interval(1)) + 𝕍₁ᴺ_2N_3N.*(l₁₂_2N./l_den_2N)' - 𝕍₂ᴺ_2N_3N.*(l₁₁_2N./l_den_2N)')

B_3N = project(B,fourier3^2,fourier3^2)
component(B_3N,1,1)[N+1:end,N+1:end] .= Diagonal(interval.(ones(2N)))
component(B_3N,2,2)[N+1:end,N+1:end] .= Diagonal(interval.(ones(2N)))

P_2N = interval.(sqrt(2)*(vec(ones(2N+1, 1))))
P_2N[1,1] = interval(1)
P_2N⁻¹ = (interval.(ones(2N+1))./P_2N)
P_3N = interval.(sqrt(2)*(vec(ones(3N+1, 1))))
P_3N[1,1] = interval(1)

Z₀ = opnorm(LinearOperator(coefficients([P_3N ; P_3N].*(UniformScaling(interval(1)) - _matprod2(B_3N,M_2N_3N)).*[P_2N⁻¹ ; P_2N⁻¹]')),2)

Z₁ = sqrt(Z₀^2 + ExactReal(2)*Z₁₁^2 + ExactReal(2)*Z₁₂^2)
@show Z₁
@info "Computing 𝒵ᵤ"   
# Computation of 𝒵ᵤ, defined in Lemma 4.8
# Computing the constants Cⱼ and a defined in Lemma 4.6.
a,C₁,C₂,C₃,C₄ = _compute_C_a(νi,ν₁i,ν₂i,ν₃i)

# Building the Fourier series of E.
E = Sequence(CosFourier(2N,π/di), interval.(zeros(2N+1)))
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

𝒵ᵤ = sqrt(interval(2))*norm_BM*sqrt(𝒵ᵤ₁^2 + 𝒵ᵤ₂^2)
@show 𝒵ᵤ

l⁻¹_norm = φ(norm_ℳ₁_𝓁⁻¹_component_1_1, norm_ℳ₁_𝓁⁻¹_component_1_2, norm_ℳ₁_𝓁⁻¹_component_2_1, norm_ℳ₁_𝓁⁻¹_component_2_2)

𝒵₁ = Z₁ + 𝒵ᵤ + norm_BM*l⁻¹_norm*sqrt(norm(V₁ᴺ_interval - V₁_interval,1)^2 + norm(V₂ᴺ_interval - V₂_interval,1)^2)

################## Computer Assisted Proof ######################################################
𝒴₀ = interval(sup(𝒴₀))
𝒵₁ = interval(sup(𝒵₁))
𝒵₂ = interval(sup(𝒵₂))
r_min = sup((interval(1) - 𝒵₁ - sqrt((interval(1) - 𝒵₁)^2 - interval(2)*𝒴₀*𝒵₂))/𝒵₂)
r_max = inf((interval(1) - 𝒵₁ + sqrt((interval(1) - 𝒵₁)^2 - interval(2)*𝒴₀*𝒵₂))/𝒵₂)
CAP(sup(𝒴₀),sup(𝒵₁),sup(𝒵₂))

r0 = r_min # radius of the ball in which the proof is done








############## Stability analysis ######################################################
# Proves the results of Theorems 6.7 and 6.8. 
# Note that these theorems are for Glycolsis and Root-Hair.
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

    𝒵23 = sqrt(𝒵₂₃) ; 

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
    while inf(real(S[k]) - ϵ*abs(S[k]+t) ) > 0
        global k, nDF
        k += 1
        nDF += 1
    end

    ### we verify that the rest of the disks is in the left half-plane
        for n = k:length(S)
            if inf(real(S[n]) + ϵ*abs(t+S[n])) >= 0
                display("The disks are not all in the left half-plane, proof of stability is inconclusive")
                return Nan
            end
        end

    display("Number of eigenvalues of DF with positive real part: $nDF")
   

