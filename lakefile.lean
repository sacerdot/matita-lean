import Lake
open Lake DSL

package «verbose-matita» where
  -- add package configuration options here

@[default_target]
lean_lib «VerboseMatita» where
  -- add library configuration options here

--@[default_target]
--lean_exe «verbose-matita» where
--  root := `Main

--require verbose from git "https://github.com/PatrickMassot/verbose-lean4.git"
