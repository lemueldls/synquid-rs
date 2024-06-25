- Get mininal example running
- `measure`s are not type-checked?
- Synqiuid synthesis goes into quickcheck generator

```mermaid
flowchart TD
  %% subgraph synquid
    %% subgraph types
      Sort


      BaseType
      subgraph TypeSkeleton
        SType
        RType
      end

      subgraph SchemaSkeleton
        SSchema
        RSchema
      end

      subgraph Program
        UProgram
        RProgram
      end

      %% Id

      %% QSpace

      Explorer

      Formula

    %% end
      Doc

    Environment

    Goal

    HornSolver

    %% Synthesis
    %% SynthesisGoal

    Z3State

    Formula+Sort{{Formula + Sort}}
    Formula+Sort+Environment{{Formula + Sort + Environment}}
    %% Formula+Id{{Formula + Id}}
    Formula+Goal{{Formula + Goal}}
    Goal+RProgram{{Goal + RProgram}}
    HornSolver+Formula{{HornSolver + Formula}}

  %% end

  subgraph z3
      z3::Sort
      z3::Ast
  end

  Ast --> Declaration
  Declaration --> Formula

  Sort --> Formula+Sort
  Formula --> Formula+Sort

  Formula+Sort --refine--> RType
  Formula+Sort --sort_substitute--> Formula

  Formula --> Formula+Goal
  Goal --> Formula+Goal

  Z3State --> HornSolver
  Formula+Goal --> RProgram

  Sort --> RType
  Formula --to_sort--> Sort
  Sort --to_z3_sort--> z3::Sort
  Formula --to_program--> RProgram
  Formula --to_ast--> z3::Ast
  z3::Ast --> z3::Sort
  BaseType --> Sort
  SSchema --> SType
  RSchema --> RType
  RSchema --> Formula
  RType --shape--> SType
  RProgram --erase_types--> UProgram

  Formula --> Formula+Sort+Environment
  Sort --> Formula+Sort+Environment
  Environment --> Formula+Sort+Environment
  Formula+Sort+Environment --generate_schema--> RSchema

  Formula -->   HornSolver+Formula
  HornSolver -->   HornSolver+Formula
  HornSolver+Formula --> RProgram

  z3 --> Z3State

  Explorer --> Goal

  Goal --> Goal+RProgram
  RProgram --> Goal+RProgram

  RType --> Explorer

  Goal+RProgram --> Doc

```

- `Formula` to `Sort`
  - Always loses information of name and value, only keeps type information.
  - Converts `Formula::Unknown`, `Formula::All(..)`, and all `Formula::BinOp` boolean operations to `Sort::Bool`.
  - Converts `Formula::BinOp(..)` arithmetic operations to `Sort::Int`.
  - Converts `Formula::Ite(..)` to only the `Sort` of the true branch.
    - Assumes both branches have the same `Sort`.
- `BaseType` to `Sort`
  - Converts `BaseType::Int` to `Sort::Int`.
  - Converts `BaseType::Bool` to `Sort::Bool`.
  - Loses representation of `Sort::Var(..)`, `Sort::Set(..)`, and `Sort::Any`.
  - Contains additional `Id` information over `Sort` for `BaseType::TypeVar(..)`.
