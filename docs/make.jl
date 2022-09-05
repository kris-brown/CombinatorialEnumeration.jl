using Documenter
using CombinatorialEnumeration

# Set Literate.jl config if not being compiled on recognized service.
config = Dict{String,String}()
if !(haskey(ENV, "GITHUB_ACTIONS") || haskey(ENV, "GITLAB_CI"))
  config["nbviewer_root_url"] = "https://nbviewer.jupyter.org/github/kris-brown/CombinatorialEnumeration.jl/blob/gh-pages/dev"
  config["repo_root_url"] = "https://github.com/kris-brown/CombinatorialEnumeration.jl/blob/main/docs"
end

makedocs(
    sitename = "CombinatorialEnumeration",
    format = Documenter.HTML(),
    modules = [CombinatorialEnumeration]
)


@info "Deploying docs"
deploydocs(
  target = "build",
  repo   = "github.com/kris-brown/CombinatorialEnumeration.jl.git",
  branch = "gh-pages",
  devbranch = "main"
)