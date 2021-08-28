using SQLite
using SQLite.Tables
include(joinpath(@__DIR__, "FLS.jl"))

fls_schema = SQLite.Tables.Schema([:ghash, :name, :jdump], [String, String, String])
premodel_schema = SQLite.Tables.Schema([:hash, :jdump, :fls], Type[String, String, Int])

function init_db(pth::Union{String,Nothing}=nothing)::Nothing
    file = pth === nothing ? joinpath(@__DIR__, "../fls.db") : pth
    println("FILE $file")
    db = SQLite.DB(file)
    SQLite.createtable!(db, "FLS", fls_schema)
    SQLite.createtable!(db, "Premodel", fls_schema)
    return nothing
end

init_db()

#add_fls(F::FLS)::Int
