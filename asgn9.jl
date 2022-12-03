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


function JYSSParse(sexp::String)::ExprC
    if (match(r"if (.+) (.+) (.+)", sexp) !== nothing)
        exp = match(r"if (.+) (.+) (.+)", sexp)
        return IfC(JYSSParse(String(exp.captures[1])), JYSSParse(String(exp.captures[2])), JYSSParse(String(exp.captures[3])))
    elseif (match(r"proc {(.+)} go {(.+)}", sexp) !== nothing)
        exp = match(r"proc {(.+)} go {(.+)}", sexp)
        return LamC(map(Symbol, String.(split(exp.captures[1]))), JYSSParse(String(exp.captures[2])))
    elseif (match(r"(.) (.+)", sexp) !== nothing)
        exp = match(r"(.) (.+)", sexp)
        return AppC(JYSSParse(String(exp.captures[1])), (convert(Vector{ExprC},map(JYSSParse, String.(split(exp.captures[2]))))))
    elseif (match(r"[0-9]+", sexp) !== nothing)
        exp = match(r"[0-9]+", sexp)
        return NumC(parse(Int8, exp.match))
    elseif (match(r"(..+)", sexp) !== nothing)
        exp = match(r"(.+)", sexp)
        return StrC(String(exp.captures[1]))
    elseif (match(r"(.)", sexp) !== nothing)
        exp = match(r"(.)", sexp)
        return IdC(Symbol(exp.captures[1]))
    end
end

println(JYSSParse("if xx yy zz"))
println(JYSSParse("proc {x y z} go {1 2 3}"))
println(JYSSParse("a b c"))
println(JYSSParse("1"))
println(JYSSParse("hi"))
println(JYSSParse("h"))
#APPC interp
function interp(app::AppC)
    f = app.fun
    a = app.args
    nums = (map(interp, a))
    if f == IdC(Symbol(+))
     sum(nums)
    elseif f == IdC(Symbol(-))
     nums[1] - nums[2]
    elseif f == IdC(Symbol(*))
     *(nums)
    elseif f == IdC(Symbol(/))
     /(nums)
    elseif (typeof(f) == NumC && length(a) == 0)
        f.n
    end
 end
#IF INTERP
function interp(ifC::IfC)
    if (checkBool(interp(ifC.cond)))
        if (ifC.cond == IdC(Symbol(true)))
            interp(ifC.thn)
        else
            interp(ifC.els)
        end
    else
        error("JYSS: Not a cond")
    # here goes the nested interp check
    #else
    #    interp(ifC.cond)
    end
end
#IDC interp
function interp(i::IdC)
    i.s
end
#NUMC INTERP
function interp(n::NumC)
    n.n
end
#NUMC INTERP
function interp(str::StrC)
    return str.val
end
#checks if the given Symbol is a bool
function checkBool(s :: Symbol)
    if (s == Symbol(true) || s == Symbol(false))
        true
    else 
        # need to interp non-symbols
        false
    end
end

# test
interp(StrC("my string"))
interp(IdC(Symbol("sym")))
interp(NumC(100))
interp(AppC(NumC(5),Vector{ExprC}()))
interp(AppC(IdC(Symbol(+)), Vector{ExprC}([NumC(1),NumC(2)])))
interp(AppC(IdC(Symbol(-)), Vector{ExprC}([NumC(1),NumC(2)])))
interp(IfC(IdC(Symbol(true)), NumC(1), NumC(0)))
