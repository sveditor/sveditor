@REM *************************************************************************
@REM * sve_collect_compiler_args
@REM *
@REM * Root script that invokes the compile command
@REM *************************************************************************

@REM Ensure that the 'wrapper' compiler scripts are found
@set sve_compiler_wrappers_dir=%~dp0
@set Path=%sve_compiler_wrappers_dir%;%Path%
@set PATH=%sve_compiler_wrappers_dir%;%PATH%


@REM IF "%SVE_COMPILER_ARGS_FILE" == "" set SVE_COMPILER_ARGS_FILE="%CD%\sve_compiler_args.f"

@REM Null out the file
@echo "[NOTE] Writing compiler files to %SVE_COMPILER_ARGS_FILE%"
@echo "" > %SVE_COMPILER_ARGS_FILE%

@REM Finally, execute the target command
@%*
