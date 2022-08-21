using Documenter
using ModelEnumeration

# Set Literate.jl config if not being compiled on recognized service.
config = Dict{String,String}()
if !(haskey(ENV, "GITHUB_ACTIONS") || haskey(ENV, "GITLAB_CI"))
  config["nbviewer_root_url"] = "https://nbviewer.jupyter.org/github/kris-brown/ModelEnumeration.jl/blob/gh-pages/dev"
  config["repo_root_url"] = "https://github.com/kris-brown/ModelEnumeration.jl/blob/main/docs"
end

makedocs(
    sitename = "ModelEnumeration",
    format = Documenter.HTML(),
    modules = [ModelEnumeration]
)


@info "Deploying docs"
deploydocs(
  target = "build",
  repo   = "github.com/kris-brown/ModelEnumeration.jl.git",
  branch = "gh-pages",
  devbranch = "main"
)