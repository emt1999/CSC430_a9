# Structure Definitions

abstract type ExprC end

struct NumC <: ExprC
    n::Real
end

struct IdC <: ExprC
    s::Symbol
end

struct StrC <: ExprC
    val::String
end

struct AppC <: ExprC
    fun::ExprC
    args::Vector{ExprC}
end

struct LamC <: ExprC
    args::Vector{Symbol}
    body::ExprC
end

struct IfC <: ExprC
    cond::ExprC
    thn::ExprC
    els::ExprC
end