#!/bin/bash
# Script version 0.2

# Wrong usage
if [[ $# -lt 1 ]]; then
    echo "Please invoke vac.sh -h for correct usage."
    exit 1
fi

# Default option for VAC
if [[ $# -eq 1 ]]; then
    if [[ $1 != '-h' ]] && [[ $1 != '--help' ]]; then
        # ARBAC File
        ARBAC_FILE=$1
        if [[ -e $ARBAC_FILE ]] && [[ -f $ARBAC_FILE ]]; then
            echo "=====> Simplification ARBAC policy =====>"
            log=$(./bin/simplify -g $ARBAC_FILE 2>&1)

            #Something go wrong with the parser
            if [[ $log =~ 'error' ]]; then
                echo $log
                echo "Please input correct ARBAC file format."
                rm -rf $ARBAC_FILE"_reduceAdmin.arbac" $ARBAC_FILE"_debug"
                exit 1
            fi

            echo "=====> Translation ARBAC policy =====>"
            ./bin/translate -f interproc -a abstract $ARBAC_FILE"_reduceAdmin.arbac"
            echo "=====> Analysis of translated ARBAC policy =====>"
            # Use interproc to analyze on Abstract translated file first
            query_answer=`./bin/interproc -domain box $ARBAC_FILE"_reduceAdmin.arbac_OverApx_INTERPROC.cpp"`
            if [[ ${query_answer} =~ 'not safe' ]]; then
                # USe CBMC to analyze on Precise translated file
                echo "The ARBAC policy may not be safe."
                echo "===> Under approximate analysis ===>"
                ./bin/translate -f cbmc -a precise $ARBAC_FILE"_reduceAdmin.arbac"
                ./bin/cbmc --unwind 2 --no-unwinding-assertions --xml-ui $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_CBMC.c" &> $ARBAC_FILE"_log.xml"
                query_answer=`./bin/counterexample $ARBAC_FILE"_log.xml" $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_CBMC.c" $ARBAC_FILE"_reduceAdmin.arbac" $ARBAC_FILE"_debug" $ARBAC_FILE`
                if [[ ${query_answer} =~ 'no Counter Example' ]]; then
                    echo "===> Complete Analysis ===>"
                    ./bin/translate -f smt -a precise $ARBAC_FILE"_reduceAdmin.arbac"
                    # Use Z3 for complete analysis
                    answer=`./bin/z3 -smt2 $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_SMT.smt2"`
                    if [[ ${answer} =~ 'unsat' ]]; then
                        ./bin/cbmc --unwind 10 --no-unwinding-assertions --xml-ui $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_CBMC.c" &> $ARBAC_FILE"_log.xml"
                        answer1=`./bin/counterexample $ARBAC_FILE"_log.xml" $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_CBMC.c" $ARBAC_FILE"_reduceAdmin.arbac" $ARBAC_FILE"_debug" $ARBAC_FILE`
                        if [[ ${answer1} =~ 'no Counter Example' ]]; then
                            echo "There is no counter example."
                            rm -rf $ARBAC_FILE"_CounterExample"
                        else
                            if [[ ${answer1} =~ 'Cannot find Counter Example' ]]; then
                                echo "Cannot find the counter example."
                                rm -rf $ARBAC_FILE"_CounterExample"
                            else
                                echo "=====> Produce Counter Example ====>"
                                cat $ARBAC_FILE"_CounterExample"
                            fi
                        fi
                    else
                        cat $ARBAC_FILE"_CounterExample"
                        echo "The ARBAC policy is safe."
                        rm -rf $ARBAC_FILE"_CounterExample"
                    fi
                    # Delete intermediate files
                    rm -rf $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_SMT.smt2"
                else
                    if [[ ${query_answer} =~ 'Cannot find Counter Example' ]]; then
                        ./bin/cbmc --unwind 10 --no-unwinding-assertions --xml-ui $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_CBMC.c" &> $ARBAC_FILE"_log.xml"
                        answer1=`./bin/counterexample $ARBAC_FILE"_log.xml" $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_CBMC.c" $ARBAC_FILE"_reduceAdmin.arbac" $ARBAC_FILE"_debug" $ARBAC_FILE`
                        if [[ ${answer1} =~ 'no Counter Example' ]]; then
                            echo "There is no counter example."
                            rm -rf $ARBAC_FILE"_CounterExample"
                        else
                            if [[ ${answer1} =~ 'Cannot find Counter Example' ]]; then
                                echo "Cannot find the counter example."
                                rm -rf $ARBAC_FILE"_CounterExample"
                            else
                                echo "=====> Produce Counter Example ====>"
                                cat $ARBAC_FILE"_CounterExample"
                            fi
                        fi
                    else
                        echo "=====> Produce Counter Example ====>"
                        cat $ARBAC_FILE"_CounterExample"
                    fi
                fi
                # Remove intermediate files
                rm -rf $ARBAC_FILE"_log.xml" $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_CBMC.c" $ARBAC_FILE"_reduceAdmin.arbac_OverApx_INTERPROC.cpp" $ARBAC_FILE"_reduceAdmin.arbac" $ARBAC_FILE"_debug"
            elif [[  ${query_answer} =~ 'safe' ]]; then
                echo "The ARBAC policy is safe."
                # Remove intermediate files
                rm -rf $ARBAC_FILE"_reduceAdmin.arbac_OverApx_INTERPROC.cpp" $ARBAC_FILE"_reduceAdmin.arbac" $ARBAC_FILE"_debug"
            else
                echo "There is something wrong with the analyzed file. Please check again."
                # Remove intermediate files
                rm -rf $ARBAC_FILE"_reduceAdmin.arbac_OverApx_INTERPROC.cpp" $ARBAC_FILE"_reduceAdmin.arbac" $ARBAC_FILE"_debug"
            fi
            exit 1
        else
            echo "Please input a valid ARBAC file."
            exit 1
        fi
    else
        echo    "* *                             VAC 1.1                           * *"
        echo    "* *                 Copyright Anna Lisa Ferrara (1),              * *"
        echo    "* *                        P. Madhusudan (2),                     * *"
        echo    "* *                        Truc L. Nguyen (3),                    * *"
        echo    "* *                    and Gennaro Parlato (3).                   * *"
        echo    "* *                                                               * *"
        echo    "* *               (1) University of Bristol (UK),                 * *"
        echo    "* *               (2) University of Illinois (USA),               * *"
        echo    "* *               (3) University of Southampton (UK).             * *"
        echo
        echo    "Usage:"
        echo
        echo    "  vac.sh [options] input_file"
        echo
        echo    "Frontend options:                   Purpose:"
        echo    "  --no-pruning                        no pruning procedure"
        echo    "  --backend=NAME                      choose backend from:"
        echo    "                                         interproc, moped, z3, cbmc,"
        echo    "                                         eldarica, hsf, nusmv, getafix, mucke"
        echo    "  --unwind=NUMBER                     unwind NUMBER times (CBMC only)"
        echo    "  --bddlib=LIB                        BDD library (MUCKE only)"
        echo    "  --mucke-rounds=NUMBER               NUMBER of rounds (MUCKE only)"
        echo    "  --formula=FOR                       custom formula for MUCKE (required)"
        echo    "  --print-pruned-policy               print simplified policy"
        echo    "  --print-translated-policy=FORMAT    print the translated program in FORMAT from:"
        echo    "                                         interproc, moped, z3, cbmc,"
        echo    "                                         eldarica, hsf, nusmv, getafix, mucke"
        echo    "  --mohawk                            print equivalent Mohawk benchmark"
        echo    "  -h, --help                          show help"
        echo
        echo
        # echo    "VAC without any option runs the default option: "
        # echo    "first run the abstract transformer followed by Interproc."
        # echo    "If a proof cannot be provided, VAC runs the precise transformer followed by CBMC"
        # echo    "(unwind set to 2) to look for a counterexample. Otherwise, it executes Z3 (muZ module) for complete analysis."
        exit 1
    fi
fi

# Specify options
PARSED_OPTIONS=$(getopt -n "$0" -a -o h -l "help,no-pruning,print-pruned-policy,print-translated-policy:,backend:,unwind:,mohawk,bddlib:,formula:,mucke-rounds:" -- "$@")

if [[ $? -ne 0 ]]; then
    echo "Please invoke vac.sh -h for correct usage."
    exit 1
fi

eval set -- "$PARSED_OPTIONS"

mucke_lib="longbman.so"
mucke_formula=""
mucke_rounds=4

while true;
do
  case "$1" in
    -h|--help)
      shift;;

    --no-pruning)
      no_pruning_flag=1
      shift;;

    --print-pruned-policy)
      print_pruned_policy_flag=1
      shift;;

    --mohawk)
      print_mohawk=1
      shift;;

    --bddlib)
      if [ -n "$2" ]; then
        mucke_lib=$2
      else
        echo "Please specify the BDD library name. Try vac.sh -h for correct usage."
        exit 1
      fi
      shift 2;;

    --formula)
      if [ -n "$2" ]; then
        mucke_formula=$2
      else
        echo "Please specify the formula name. Try vac.sh -h for correct usage."
        exit 1
      fi
      shift 2;;

    --mucke-rounds)
      if [ -n "$2" ]; then
        mucke_rounds=$2
      else
        echo "Please specify the mucke number of rounds. Try vac.sh -h for correct usage."
        exit 1
      fi
      shift 2;;


    --print-translated-policy)
      print_translated_policy_flag=1
      if [ -n "$2" ]; then
        format=$2
      else
        echo "Please specify the FORMAT of translated program. Try vac.sh -h for correct usage."
        exit 1
      fi
      shift 2;;

    --backend)
      if [ -n "$2" ]; then
        backend=$2
      else
        echo "Please specify the backend name. Try vac.sh -h for correct usage."
        exit 1
      fi
      shift 2;;

    --unwind)
      flag=1
      if [ -n "$2" ]; then
        unwind=$2
      else
        echo "Please specify the number of unwind loop for CBMC. Try vac.sh -h for correct usage."
        exit 1
      fi
      shift 2;;

    --)
      ARBAC_FILE=$2
      shift
      break;;
  esac
done

if [[ -e $ARBAC_FILE ]] && [[ -f $ARBAC_FILE ]]; then
    if [[ $print_mohawk -eq 1 ]]; then
        log=$(./bin/simplify -m $ARBAC_FILE 2>&1)
        if [[ $log =~ 'error' ]]; then
            echo $log
            echo "Please input correct ARBAC file format."
            rm -rf $ARBAC_FILE"_mohawk.arbac"
            exit 1
        fi
        cat $ARBAC_FILE"_mohawk.arbac"
        echo
        echo
        exit 1
    fi

    # Print simplified ARBAC policy
    if [[ $print_pruned_policy_flag -eq 1 ]]; then
        echo
        if [[ $print_translated_policy_flag -eq 1 ]]; then
            echo "Please choose either printing pruned policy or translated policy."
            exit 1
        fi
        if [[ $no_pruning_flag -eq 1 ]]; then
            echo "Cannot print pruned policy when choosing no-pruning options."
            echo "Please invoke vac.sh -h for correct usage."
            exit 1
        fi
        log=$(./bin/simplify $ARBAC_FILE 2>&1)
        if [[ $log =~ 'error' ]]; then
            echo $log
            echo "Please input correct ARBAC file format."
            rm -rf $ARBAC_FILE"_reduceAdmin.arbac"
            exit 1
        fi
        cat $ARBAC_FILE"_reduceAdmin.arbac"
        echo
        echo
        exit 1
    fi

    # Print translated policy
    if [[ $print_translated_policy_flag -eq 1 ]]; then
        echo
        if [[ $print_pruned_policy_flag -eq 1 ]]; then
            echo "Please choose printing either pruned policy or translated policy."
            exit 1
        fi
        case "$format" in
            interproc)
                if [[ $no_pruning_flag -eq 1 ]]; then
                    log2=$(./bin/translate -f interproc -a abstract $ARBAC_FILE 2>&1)
                    if [[ $log2 =~ 'error' ]]; then
                        echo $log2
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_OverApx_INTERPROC.cpp"
                        exit 1
                    fi
                    cat $ARBAC_FILE"_OverApx_INTERPROC.cpp"
                else
                    log=$(./bin/simplify $ARBAC_FILE 2>&1)
                    if [[ $log =~ 'error' ]]; then
                        echo $log
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_reduceAdmin.arbac"
                        exit 1
                    fi
                    ./bin/translate -f interproc -a abstract $ARBAC_FILE"_reduceAdmin.arbac"
                    cat $ARBAC_FILE"_reduceAdmin.arbac_OverApx_INTERPROC.cpp"
                fi
                ;;
            cbmc)
                if [[ $no_pruning_flag -eq 1 ]]; then
                    log2=$(./bin/translate -f cbmc -a precise $ARBAC_FILE 2>&1)
                    if [[ $log2 =~ 'error' ]]; then
                        echo $log2
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_ExactAlg_CBMC.c"
                        exit 1
                    fi
                    cat $ARBAC_FILE"_ExactAlg_CBMC.c"
                else
                    log=$(./bin/simplify $ARBAC_FILE 2>&1)
                    if [[ $log =~ 'error' ]]; then
                        echo $log
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_reduceAdmin.arbac"
                        exit 1
                    fi
                    ./bin/translate -f cbmc -a precise $ARBAC_FILE"_reduceAdmin.arbac"
                    cat $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_CBMC.c"
                fi
                ;;
            moped)
                if [[ $no_pruning_flag -eq 1 ]]; then
                    log2=$(./bin/translate -f moped -a precise $ARBAC_FILE 2>&1)
                    if [[ $log2 =~ 'error' ]]; then
                        echo $log2
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_ExactAlg_GETAFIX.bp"
                        exit 1
                    fi
                    cat $ARBAC_FILE"_ExactAlg_GETAFIX.bp"
                else
                    log=$(./bin/simplify $ARBAC_FILE 2>&1)
                    if [[ $log =~ 'error' ]]; then
                        echo $log
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_reduceAdmin.arbac"
                        exit 1
                    fi
                    ./bin/translate -f moped -a precise $ARBAC_FILE"_reduceAdmin.arbac"
                    cat $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_GETAFIX.bp"
                fi
                ;;
            getafix)
                if [[ $no_pruning_flag -eq 1 ]]; then
                    log2=$(./bin/translate -f getafix -a precise $ARBAC_FILE 2>&1)
                    if [[ $log2 =~ 'error' ]]; then
                        echo $log2
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_ExactAlg_parallel_GETAFIX.bp"
                        exit 1
                    fi
                    cat $ARBAC_FILE"_ExactAlg_parallel_GETAFIX.bp"
                else
                    log=$(./bin/simplify $ARBAC_FILE 2>&1)
                    if [[ $log =~ 'error' ]]; then
                        echo $log
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_reduceAdmin.arbac"
                        exit 1
                    fi
                    ./bin/translate -f getafix -a precise $ARBAC_FILE"_reduceAdmin.arbac"
                    cat $ARBAC_FILE"_ExactAlg_parallel_GETAFIX.bp"
                fi
                ;;
            mucke)
                if [[ -z $mucke_formula ]]; then
                    echo "Please set formula for MUCKE"
                    exit 1
                fi
                if [[ $mucke_rounds -lt 1 ]]; then
                    echo "MUCKE number of rounds must be greater than 0"
                    exit 1
                fi
                if [[ $no_pruning_flag -eq 1 ]]; then
                    log2=$(./bin/translate -f mucke -a precise -l $mucke_formula -r $mucke_rounds $ARBAC_FILE 2>&1)
                    if [[ $log2 =~ 'error' ]]; then
                        echo $log2
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_ExactAlg_MUCKE.mu"
                        exit 1
                    fi
                    cat $ARBAC_FILE"_ExactAlg_MUCKE.mu"
                else
                    log=$(./bin/simplify $ARBAC_FILE 2>&1)
                    if [[ $log =~ 'error' ]]; then
                        echo $log
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_reduceAdmin.arbac"
                        exit 1
                    fi
                    ./bin/translate -f mucke -a precise -l $mucke_formula -r $mucke_rounds $ARBAC_FILE"_reduceAdmin.arbac"
                    cat $ARBAC_FILE"_ExactAlg_MUCKE.mu"
                fi
                ;;
            z3)
                if [[ $no_pruning_flag -eq 1 ]]; then
                    log2=$(./bin/translate -f smt -a precise $ARBAC_FILE 2>&1)
                    if [[ $log2 =~ 'error' ]]; then
                        echo $log2
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_ExactAlg_SMT.smt2"
                        exit 1
                    fi
                    cat $ARBAC_FILE"_ExactAlg_SMT.smt2"
                else
                    log=$(./bin/simplify $ARBAC_FILE 2>&1)
                    if [[ $log =~ 'error' ]]; then
                        echo $log
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_reduceAdmin.arbac"
                        exit 1
                    fi
                    ./bin/translate -f smt -a precise $ARBAC_FILE"_reduceAdmin.arbac"
                    cat $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_SMT.smt2"
                fi
                ;;
            hsf)
                if [[ $no_pruning_flag -eq 1 ]]; then
                    log2=$(./bin/translate -f hsf -a precise $ARBAC_FILE 2>&1)
                    if [[ $log2 =~ 'error' ]]; then
                        echo $log2
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_ExactAlg_HSF.qarmc"
                        exit 1
                    fi
                    cat $ARBAC_FILE"_ExactAlg_HSF.qarmc"
                else
                    log=$(./bin/simplify $ARBAC_FILE 2>&1)
                    if [[ $log =~ 'error' ]]; then
                        echo $log
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_reduceAdmin.arbac"
                        exit 1
                    fi
                    ./bin/translate -f hsf -a precise $ARBAC_FILE"_reduceAdmin.arbac"
                    cat $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_HSF.qarmc"
                fi
                ;;
            eldarica)
                if [[ $no_pruning_flag -eq 1 ]]; then
                    log2=$(./bin/translate -f eldarica -a precise $ARBAC_FILE 2>&1)
                    if [[ $log2 =~ 'error' ]]; then
                        echo $log2
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_ExactAlg_ELDARICA.horn"
                        exit 1
                    fi
                    cat $ARBAC_FILE"_ExactAlg_ELDARICA.horn"
                else
                    log=$(./bin/simplify $ARBAC_FILE 2>&1)
                    if [[ $log =~ 'error' ]]; then
                        echo $log
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_reduceAdmin.arbac"
                        exit 1
                    fi
                    ./bin/translate -f eldarica -a precise $ARBAC_FILE"_reduceAdmin.arbac"
                    cat $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_ELDARICA.horn"
                fi
                ;;
            nusmv)
                if [[ $no_pruning_flag -eq 1 ]]; then
                    log2=$(./bin/translate -f nusmv -a precise $ARBAC_FILE 2>&1)
                    if [[ $log2 =~ 'error' ]]; then
                        echo $log2
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_ExactAlg_NuSMV.smv"
                        exit 1
                    fi
                    cat $ARBAC_FILE"_ExactAlg_NuSMV.smv"
                else
                    log=$(./bin/simplify $ARBAC_FILE 2>&1)
                    if [[ $log =~ 'error' ]]; then
                        echo $log
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_reduceAdmin.arbac"
                        exit 1
                    fi
                    ./bin/translate -f nusmv -a precise $ARBAC_FILE"_reduceAdmin.arbac"
                    cat $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_NuSMV.smv"
                fi
                ;;
            *)
                echo "Please specify the correct FORMAT for the translation."
                exit 1
                ;;
        esac
        echo
        if [[ $no_pruning_flag -ne 1 ]]; then
            rm -rf $ARBAC_FILE"_reduceAdmin.arbac"
        fi
        exit 1
    fi

    if [[ $print_pruned_policy_flag -ne 1 ]] && [[ $print_translated_policy_flag -ne 1 ]]; then
        # Choose the backend to verify
        case $backend in
            interproc)
                if [[ $no_pruning_flag -eq 1 ]]; then
                    echo "=====> Translation ARBAC policy =====>"
                    log3=$(./bin/translate -f interproc -a abstract $ARBAC_FILE 2>&1)
                    if [[ $log3 =~ 'error' ]]; then
                        echo $log3
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_OverApx_INTERPROC.cpp"
                        exit 1
                    fi
                    echo "=====> Analysis of translated ARBAC policy =====>"
                    # Use interproc to analyze on Abstract translated file
                    query_answer=`./bin/interproc -domain box $ARBAC_FILE"_OverApx_INTERPROC.cpp"`
                    if [[ ${query_answer} =~ 'not safe' ]]; then
                        echo "The ARBAC policy may not be safe."
                    elif [[ ${query_answer} =~ 'safe' ]]; then
                        #statements
                        echo "The ARBAC policy is safe."
                    else
                        echo "There is something wrong with the analyzed file. Please check again."
                    fi
                    # Remove intermediate files
                    rm -rf $ARBAC_FILE"_OverApx_INTERPROC.cpp"
                else
                    echo "=====> Simplification ARBAC policy =====>"
                    log=$(./bin/simplify -g $ARBAC_FILE 2>&1)
                    if [[ $log =~ 'error' ]]; then
                        echo $log
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_reduceAdmin.arbac" $ARBAC_FILE"_debug"
                        exit 1
                    fi
                    echo "=====> Translation ARBAC policy =====>"
                    ./bin/translate -f interproc -a abstract $ARBAC_FILE"_reduceAdmin.arbac"
                    echo "=====> Analysis of translated ARBAC policy =====>"
                    # Use interproc to analyze on Abstract translated file
                    query_answer=`./bin/interproc -domain box $ARBAC_FILE"_reduceAdmin.arbac_OverApx_INTERPROC.cpp"`
                    if [[ ${query_answer} =~ 'not safe' ]]; then
                        echo "The ARBAC policy may not be safe."
                    elif [[ ${query_answer} =~ 'safe' ]]; then
                        #statements
                        echo "The ARBAC policy is safe."
                    else
                        echo "There is something wrong with the analyzed file. Please check again."
                    fi
                    # Remove intermediate files
                    rm -rf $ARBAC_FILE"_reduceAdmin.arbac_OverApx_INTERPROC.cpp"
                fi
                ;;
            cbmc)
                if [[ $flag -eq 0 ]]; then
                    echo "Please specify the number of unwinding loop for CBMC."
                    if [[ $no_pruning_flag -ne 1 ]]; then
                        rm -rf $ARBAC_FILE"_reduceAdmin.arbac" $ARBAC_FILE"_debug"
                    fi
                    exit 1
                fi
                if [[ $no_pruning_flag -eq 1 ]]; then
                    echo "=====> Translation ARBAC policy =====>"
                    log3=$(./bin/translate -f cbmc -a precise $ARBAC_FILE 2>&1)
                    if [[ $log3 =~ 'error' ]]; then
                        echo $log3
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_ExactAlg_CBMC.c"
                        exit 1
                    fi
                    echo "=====> Analysis of translated ARBAC policy =====>"
                    # Use CBMC to analyze on Precise translated file
                    query_answer=`./bin/cbmc --unwind $unwind --no-unwinding-assertions $ARBAC_FILE"_ExactAlg_CBMC.c"`
                    if [[ ${query_answer} =~ 'VERIFICATION SUCCESSFUL' ]]; then
                        echo "The ARBAC policy may be safe at bound $unwind of unwinding."
                    elif [[ ${query_answer} =~ 'VERIFICATION FAILED' ]]; then
                        echo "The ARBAC policy is not safe."
                    else
                        echo "There is something wrong with the analyzed file. Please check again."
                    fi
                    # Remove intermediate files
                    rm -rf $ARBAC_FILE"_ExactAlg_CBMC.c"
                else
                    echo "=====> Simplification ARBAC policy =====>"
                    log=$(./bin/simplify -g $ARBAC_FILE 2>&1)
                    if [[ $log =~ 'error' ]]; then
                        echo $log
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_reduceAdmin.arbac" $ARBAC_FILE"_debug"
                        exit 1
                    fi
                    echo "=====> Translation ARBAC policy =====>"
                    ./bin/translate -f cbmc -a precise $ARBAC_FILE"_reduceAdmin.arbac"
                    echo "=====> Analysis of translated ARBAC policy =====>"
                    # Use CBMC to analyze on Precise translated file
                    ./bin/cbmc --unwind $unwind --no-unwinding-assertions --xml-ui $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_CBMC.c" &> $ARBAC_FILE"_log.xml"
                    query_answer=`./bin/counterexample $ARBAC_FILE"_log.xml" $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_CBMC.c" $ARBAC_FILE"_reduceAdmin.arbac" $ARBAC_FILE"_debug" $ARBAC_FILE`
                    if [[ ${query_answer} =~ 'no Counter Example' ]]; then
                        echo "The ARBAC policy may be safe at bound $unwind of unwinding."
                        rm -rf $ARBAC_FILE"_CounterExample"
                    else
                        if [[ ${query_answer} =~ 'Cannot find Counter Example' ]]; then
                            echo "Cannot find counter example at bound $unwind of unwinding."
                            rm -rf $ARBAC_FILE"_CounterExample"
                        else
                            echo "The ARBAC policy is not safe."
                            cat $ARBAC_FILE"_CounterExample"
                        fi
                    fi
                    # Remove intermediate files
                    rm -rf $ARBAC_FILE"_log.xml" $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_CBMC.c"
                fi
                ;;
            moped)
                if [[ $no_pruning_flag -eq 1 ]]; then
                    echo "=====> Translation ARBAC policy =====>"
                    log3=$(./bin/translate -f moped -a precise $ARBAC_FILE 2>&1)
                    if [[ $log3 =~ 'error' ]]; then
                        echo $log3
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_ExactAlg_GETAFIX.bp"
                        exit 1
                    fi
                    echo "=====> Analysis of translated ARBAC policy =====>"
                    # Use MOPED to analyze on Abstract translated file first
                    query_answer=`./bin/moped -b $ARBAC_FILE"_ExactAlg_GETAFIX.bp"`
                    if [[ ${query_answer} =~ 'Not reachable.' ]]; then
                        echo "The ARBAC policy is safe."
                    elif [[ ${query_answer} =~ 'Reachable.' ]]; then
                        echo "The ARBAC policy is not safe."
                    else
                        echo "There is something wrong with the analyzed file. Please check again."
                    fi
                    # Remove intermediate files
                    rm -rf $ARBAC_FILE"_ExactAlg_GETAFIX.bp"
                else
                    echo "=====> Simplification ARBAC policy =====>"
                    log=$(./bin/simplify -g $ARBAC_FILE 2>&1)
                    if [[ $log =~ 'error' ]]; then
                        echo $log
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_reduceAdmin.arbac" $ARBAC_FILE"_debug"
                        exit 1
                    fi
                    echo "=====> Translation ARBAC policy =====>"
                    ./bin/translate -f moped -a precise $ARBAC_FILE"_reduceAdmin.arbac"
                    echo "=====> Analysis of translated ARBAC policy =====>"
                    # Use MOPED to analyze on Abstract translated file first
                    query_answer=`./bin/moped -b $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_GETAFIX.bp"`
                    if [[ ${query_answer} =~ 'Not reachable.' ]]; then
                        echo "The ARBAC policy is safe."
                    elif [[ ${query_answer} =~ 'Reachable.' ]]; then
                        echo "The ARBAC policy is not safe."
                    else
                        echo "There is something wrong with the analyzed file. Please check again."
                    fi
                    # Remove intermediate files
                    rm -rf $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_GETAFIX.bp"
                fi
                ;;
            getafix)
                if [[ $no_pruning_flag -eq 1 ]]; then
                    echo "=====> Translation ARBAC policy =====>"
                    log3=$(./bin/translate -f getafix -a precise $ARBAC_FILE 2>&1)
                    if [[ $log3 =~ 'error' ]]; then
                        echo $log3
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_ExactAlg_parallel_GETAFIX.bp"
                        exit 1
                    fi
                    echo "=====> Analysis of translated ARBAC policy =====>"
                    # Use GETAFIX to analyze on Abstract translated file first
                    query_answer=`./bin/getafix -b $ARBAC_FILE"_ExactAlg_parallel_GETAFIX.bp"`
                    if [[ ${query_answer} =~ 'Not reachable.' ]]; then
                        echo "The ARBAC policy is safe."
                    elif [[ ${query_answer} =~ 'Reachable.' ]]; then
                        echo "The ARBAC policy is not safe."
                    else
                        echo "There is something wrong with the analyzed file. Please check again."
                    fi
                    # Remove intermediate files
                    rm -rf $ARBAC_FILE"_ExactAlg_parallel_GETAFIX.bp"
                else
                    echo "=====> Simplification ARBAC policy =====>"
                    log=$(./bin/simplify -g $ARBAC_FILE 2>&1)
                    if [[ $log =~ 'error' ]]; then
                        echo $log
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_reduceAdmin.arbac" $ARBAC_FILE"_debug"
                        exit 1
                    fi
                    echo "=====> Translation ARBAC policy =====>"
                    ./bin/translate -f getafix -a precise $ARBAC_FILE"_reduceAdmin.arbac"
                    echo "=====> Analysis of translated ARBAC policy =====>"
                    # Use GETAFIX to analyze on Abstract translated file first
                    query_answer=`./bin/getafix -b $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_parallel_GETAFIX.bp"`
                    if [[ ${query_answer} =~ 'Not reachable.' ]]; then
                        echo "The ARBAC policy is safe."
                    elif [[ ${query_answer} =~ 'Reachable.' ]]; then
                        echo "The ARBAC policy is not safe."
                    else
                        echo "There is something wrong with the analyzed file. Please check again."
                    fi
                    # Remove intermediate files
                    rm -rf $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_parallel_GETAFIX.bp"
                fi
                ;;
            mucke)
                if [[ -z $mucke_formula ]]; then
                    echo "Please set formula for MUCKE"
                    exit 1
                fi
                if [[ $mucke_rounds -lt 1 ]]; then
                    echo "MUCKE number of rounds must be greater than 0"
                    exit 1
                fi
                if [[ $no_pruning_flag -eq 1 ]]; then
                    echo "=====> Translation ARBAC policy =====>"
                    log3=$(./bin/translate -f mucke -a precise -l $mucke_formula -r $mucke_rounds $ARBAC_FILE 2>&1)
                    if [[ $log3 =~ 'error' ]]; then
                        echo $log3
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_ExactAlg_MUCKE.mu"
                        exit 1
                    fi
                    echo "=====> Analysis of translated ARBAC policy =====>"
                    # Use MUCKE to analyze on Abstract translated file first
                    query_answer=`./bin/mucke -res -bman $mucke_lib $ARBAC_FILE"_ExactAlg_MUCKE.mu"`
                    if [[ ${query_answer} =~ ':   false' ]]; then
                        echo "The ARBAC policy may be safe."
                    elif [[ ${query_answer} =~ ':   true' ]]; then
                        echo "The ARBAC policy is not safe."
                    else
                        echo "There is something wrong with the analyzed file. Please check again."
                    fi
                    # Remove intermediate files
                    echo "${query_answer}" > $ARBAC_FILE"_ExactAlg_MUCKE.mu.log"
                    # rm -rf $ARBAC_FILE"_ExactAlg_MUCKE.mu"
                else
                    echo "=====> Simplification ARBAC policy =====>"
                    log=$(./bin/simplify -g $ARBAC_FILE 2>&1)
                    if [[ $log =~ 'error' ]]; then
                        echo $log
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_reduceAdmin.arbac" $ARBAC_FILE"_debug"
                        exit 1
                    fi
                    echo "=====> Translation ARBAC policy =====>"
                    ./bin/translate -f mucke -a precise -l $mucke_formula -r $mucke_rounds $ARBAC_FILE"_reduceAdmin.arbac"
                    echo "=====> Analysis of translated ARBAC policy =====>"
                    # Use MUCKE to analyze on Abstract translated file first
                    query_answer=`./bin/mucke -res -bman $mucke_lib $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_MUCKE.mu"`
                    if [[ ${query_answer} =~ ':   false' ]]; then
                        echo "The ARBAC policy may be safe."
                    elif [[ ${query_answer} =~ ':   true' ]]; then
                        echo "The ARBAC policy is not safe."
                    else
                        echo "There is something wrong with the analyzed file. Please check again."
                    fi
                    # Remove intermediate files
                    echo "${query_answer}" > $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_MUCKE.mu.log"
                    # rm -rf $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_MUCKE.mu"
                fi
                ;;
            z3)
                if [[ $no_pruning_flag -eq 1 ]]; then
                    echo "=====> Translation ARBAC policy =====>"
                    log3=$(./bin/translate -f smt -a precise $ARBAC_FILE 2>&1)
                    if [[ $log3 =~ 'error' ]]; then
                        echo $log3
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_ExactAlg_SMT.smt2"
                        exit 1
                    fi
                    echo "=====> Analysis of translated ARBAC policy =====>"
                    # Use Z3 to analyze on Abstract translated file first
                    query_answer=`./bin/z3 -smt2 $ARBAC_FILE"_ExactAlg_SMT.smt2"`
                    if [[ ${query_answer} =~ 'unsat' ]]; then
                        echo "The ARBAC policy is not safe."
                    elif [[ ${query_answer} =~ 'sat' ]]; then
                        echo "The ARBAC policy is safe."
                    else
                        echo "There is something wrong with the analyzed file. Please check again."
                    fi
                    # Remove intermediate files
                    rm -rf $ARBAC_FILE"_ExactAlg_SMT.smt2"

                else
                    echo "=====> Simplification ARBAC policy =====>"
                    log=$(./bin/simplify -g $ARBAC_FILE 2>&1)
                    if [[ $log =~ 'error' ]]; then
                        echo $log
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_reduceAdmin.arbac" $ARBAC_FILE"_debug"
                        exit 1
                    fi
                    echo "=====> Translation ARBAC policy =====>"
                    ./bin/translate -f smt -a precise $ARBAC_FILE"_reduceAdmin.arbac"
                    echo "=====> Analysis of translated ARBAC policy =====>"
                    # Use Z3 to analyze on Abstract translated file first
                    query_answer=`./bin/z3 -smt2 $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_SMT.smt2"`
                    if [[ ${query_answer} =~ 'unsat' ]]; then
                        echo "The ARBAC policy is not safe."
                    elif [[ ${query_answer} =~ 'sat' ]]; then
                        echo "The ARBAC policy is safe."
                    else
                        echo "There is something wrong with the analyzed file. Please check again."
                    fi
                    # Remove intermediate files
                    rm -rf $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_SMT.smt2"
                fi
                ;;
            hsf)
                if [[ $no_pruning_flag -eq 1 ]]; then
                    echo "=====> Translation ARBAC policy =====>"
                    log3=$(./bin/translate -f hsf -a precise $ARBAC_FILE 2>&1)
                    if [[ $log3 =~ 'error' ]]; then
                        echo $log3
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_ExactAlg_HSF.qarmc"
                        exit 1
                    fi
                    echo "=====> Analysis of translated ARBAC policy =====>"
                    # Use QARMC to analyze on Abstract translated file first
                    query_answer=`./bin/qarmc $ARBAC_FILE"_ExactAlg_HSF.qarmc"`
                    if [[ ${query_answer} =~ 'not correct' ]]; then
                        echo "The ARBAC policy is not safe."
                    elif [[ ${query_answer} =~ 'correct' ]]; then
                        echo "The ARBAC policy is safe."
                    else
                        echo "There is something wrong with the analyzed file. Please check again."
                    fi
                    # Remove intermediate files
                    rm -rf $ARBAC_FILE"_ExactAlg_HSF.qarmc"
                else
                    echo "=====> Simplification ARBAC policy =====>"
                    log=$(./bin/simplify -g $ARBAC_FILE 2>&1)
                    if [[ $log =~ 'error' ]]; then
                        echo $log
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_reduceAdmin.arbac" $ARBAC_FILE"_debug"
                        exit 1
                    fi
                    echo "=====> Translation ARBAC policy =====>"
                    ./bin/translate -f hsf -a precise $ARBAC_FILE"_reduceAdmin.arbac"
                    echo "=====> Analysis of translated ARBAC policy =====>"
                    # Use QARMC to analyze on Abstract translated file first
                    query_answer=`./bin/qarmc $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_HSF.qarmc"`
                    if [[ ${query_answer} =~ 'not correct' ]]; then
                        echo "The ARBAC policy is not safe."
                    elif [[ ${query_answer} =~ 'correct' ]]; then
                        echo "The ARBAC policy is safe."
                    else
                        echo "There is something wrong with the analyzed file. Please check again."
                    fi
                    # Remove intermediate files
                    rm -rf $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_HSF.qarmc"
                fi
                ;;
            eldarica)
                if [[ $no_pruning_flag -eq 1 ]]; then
                    echo "=====> Translation ARBAC policy =====>"
                    log3=$(./bin/translate -f eldarica -a precise $ARBAC_FILE 2>&1)
                    if [[ $log3 =~ 'error' ]]; then
                        echo $log3
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_ExactAlg_ELDARICA.horn"
                        exit 1
                    fi
                    echo "=====> Analysis of translated ARBAC policy =====>"
                    # Use ELDARICA to analyze on Abstract translated file first
                    query_answer=`java -jar ./bin/eldarica-2063.jar -horn -hin -princess -bup -n $ARBAC_FILE"_ExactAlg_ELDARICA.horn"`
                    if [[ ${query_answer} =~ 'NOT SOLVABLE' ]]; then
                        echo "The ARBAC policy is not safe. Generating counter example."
                    elif [[ ${query_answer} =~ 'SOLVABLE' ]]; then
                        echo "The ARBAC policy is safe."
                    else
                        echo "There is something wrong with the analyzed file. Please check again."
                    fi
                    # Remove intermediate files
                    rm -rf $ARBAC_FILE"_ExactAlg_ELDARICA.horn"
                else
                    echo "=====> Simplification ARBAC policy =====>"
                    log=$(./bin/simplify -g $ARBAC_FILE 2>&1)
                    if [[ $log =~ 'error' ]]; then
                        echo $log
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_reduceAdmin.arbac" $ARBAC_FILE"_debug"
                        exit 1
                    fi
                    echo "=====> Translation ARBAC policy =====>"
                    ./bin/translate -f eldarica -a precise $ARBAC_FILE"_reduceAdmin.arbac"
                    echo "=====> Analysis of translated ARBAC policy =====>"
                    # Use ELDARICA to analyze on Abstract translated file first
                    query_answer=`java -jar ./bin/eldarica-2063.jar -horn -hin -princess -bup -n $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_ELDARICA.horn"`
                    if [[ ${query_answer} =~ 'NOT SOLVABLE' ]]; then
                        echo "The ARBAC policy is not safe. Generating counter example."
                    elif [[ ${query_answer} =~ 'SOLVABLE' ]]; then
                        echo "The ARBAC policy is safe."
                    else
                        echo "There is something wrong with the analyzed file. Please check again."
                    fi
                    # Remove intermediate files
                    rm -rf $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_ELDARICA.horn"
                fi
                ;;
            nusmv)
                if [[ $no_pruning_flag -eq 1 ]]; then
                    echo "=====> Translation ARBAC policy =====>"
                    log3=$(./bin/translate -f nusmv -a precise $ARBAC_FILE 2>&1)
                    if [[ $log3 =~ 'error' ]]; then
                        echo $log3
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_ExactAlg_NuSMV.smv"
                        exit 1
                    fi
                    echo "=====> Analysis of translated ARBAC policy =====>"
                    # Use ELDARICA to analyze on Abstract translated file first
                    query_answer=`./bin/NuSMV $ARBAC_FILE"_ExactAlg_NuSMV.smv"`
                    if [[ ${query_answer} =~ 'is false' ]]; then
                        echo "The ARBAC policy is not safe."
                    elif [[ ${query_answer} =~ 'is true' ]]; then
                        echo "The ARBAC policy is safe."
                    else
                        echo "There is something wrong with the analyzed file. Please check again."
                    fi
                    # Remove intermediate files
                    rm -rf $ARBAC_FILE"_ExactAlg_NuSMV.smv"
                else
                    echo "=====> Simplification ARBAC policy =====>"
                    log=$(./bin/simplify -g $ARBAC_FILE 2>&1)
                    if [[ $log =~ 'error' ]]; then
                        echo $log
                        echo "Please input correct ARBAC file format."
                        rm -rf $ARBAC_FILE"_reduceAdmin.arbac" $ARBAC_FILE"_debug"
                        exit 1
                    fi
                    echo "=====> Translation ARBAC policy =====>"
                    ./bin/translate -f nusmv -a precise $ARBAC_FILE"_reduceAdmin.arbac"
                    echo "=====> Analysis of translated ARBAC policy =====>"
                    # Use ELDARICA to analyze on Abstract translated file first
                    query_answer=`./bin/NuSMV $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_NuSMV.smv"`
                    if [[ ${query_answer} =~ 'is false' ]]; then
                        echo "The ARBAC policy is not safe."
                    elif [[ ${query_answer} =~ 'is true' ]]; then
                        echo "The ARBAC policy is safe."
                    else
                        echo "There is something wrong with the analyzed file. Please check again."
                    fi
                    # Remove intermediate files
                    rm -rf $ARBAC_FILE"_reduceAdmin.arbac_ExactAlg_NuSMV.smv"
                fi
                ;;
            *)
                echo "Please specify the correct backend name for VAC."
                exit 1
                ;;
        esac
        if [[ $no_pruning_flag -ne 1 ]]; then
            rm -rf $ARBAC_FILE"_reduceAdmin.arbac" $ARBAC_FILE"_debug"
        fi
        exit 1
    fi
else
    echo "Please input a valid ARBAC file."
    exit 1
fi


