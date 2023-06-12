## CEval

Strongly typed C interpreter. Compile with GHC 9.0.2.

Coursework. See [report.pdf](./report.pdf) for my report (Chinese). Part of the report was written merely to meet the course requirements.

All goals accomplished. May well typedness be with me.

<!-- ### TODO

- More operators (Done)

- Redefinition check

- Main function check (Done)

- Const expression

- Function (Done)
    
    - Definition (And global variable definition)

    - Call (By reference and value)

- HowTo (Done)

    1. Global var as global context & initial value

    2. Function as `Function globalCtx x`

    3. While processing, maintain:

        - `Map Name (Function globalCtx)`

        - `Renaming globalCtx currentCtx`, thus renaming function any time to `Function currentCtx x` (or `Map Name (Function currentCtx)` directly?)

    4. How to apply a `Function currentCtx`:

        - `Fun` -> `ERun`

        - `Arg, arg val` -> `\stmts -> Def arg val stmts :. Empty`

        - `Ref, var` -> `renStmtBlock (renw id var)` -->
