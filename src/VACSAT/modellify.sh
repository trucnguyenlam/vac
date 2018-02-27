#!/usr/bin/env bash

if [ -z "${1}" ]
then
      echo "No file is specified"
      echo "USAGE: ./${0} file_name"
      exit
fi

if [ ! -f "${1}" ]; then
    echo "File ${1} not found!"
    exit
fi


in_f="${1}"
tmp="${in_f}1"

# get rid of "() Bool" adding trailing "  :  "
sed 's/ () Bool/  :  /g' "${in_f}" > "${tmp}"
mv "${tmp}" "${in_f}"
# get rid of "(() (_ BitVec \d+))" adding trailing "  :  "
sed 's/ () (_ BitVec [[:digit:]]\+)/  :  /g' "${in_f}" > "${tmp}"
mv "${tmp}" "${in_f}"
# get rid of "  (define-fun " 
sed 's/  (define-fun //g' "${in_f}" > "${tmp}"
mv "${tmp}" "${in_f}"

# fixing leading 0 in var indexes
sed 's/\([^ ]\+\)_\([0-9]  \)/\1_000\2/g' "${in_f}" > "${tmp}"
mv "${tmp}" "${in_f}"
sed 's/\([^ ]\+\)_\([0-9][0-9]  \)/\1_00\2/g' "${in_f}" > "${tmp}"
mv "${tmp}" "${in_f}"
sed 's/\([^ ]\+\)_\([0-9][0-9][0-9]  \)/\1_0\2/g' "${in_f}" > "${tmp}"
mv "${tmp}" "${in_f}"
# copying indices before variable names
sed 's/\([^ ]\+\)_\([0-9][0-9][0-9][0-9]\)  /\2: \1_\2  /g' "${in_f}" > "${tmp}"
mv "${tmp}" "${in_f}"

# fixing leading 0 in |comment| indexes
sed 's/|\([^|]\+\)_\([0-9]|  \)/|\1_000\2/g' "${in_f}" > "${tmp}"
mv "${tmp}" "${in_f}"
sed 's/|\([^|]\+\)_\([0-9][0-9]|  \)/|\1_00\2/g' "${in_f}" > "${tmp}"
mv "${tmp}" "${in_f}"
sed 's/|\([^|]\+\)_\([0-9][0-9][0-9]|  \)/|\1_0\2/g' "${in_f}" > "${tmp}"
mv "${tmp}" "${in_f}"
# copying indices before variable names
sed 's/|\([^|]\+\)_\([0-9][0-9][0-9][0-9]\)|  /\2: |\1_\2|  /g' "${in_f}" > "${tmp}"
mv "${tmp}" "${in_f}"

# removing new_line between var and value
sed ':a;N;$!ba;s/  :  \n    /: /g' "${in_f}" > "${tmp}"
mv "${tmp}" "${in_f}"

# removing "(model"
sed 's/(model $//' "${in_f}" > "${tmp}"
mv "${tmp}" "${in_f}"
# removing "sat"
sed 's/sat$//' "${in_f}" > "${tmp}"
mv "${tmp}" "${in_f}"
# removing last ")"
sed 's/.$//' "${in_f}" > "${tmp}"
mv "${tmp}" "${in_f}"

# removing empty lines
sed '/^\s*$/d' "${in_f}" > "${tmp}"
mv "${tmp}" "${in_f}"

# sorting the file
sort "${in_f}" > "${tmp}"
mv "${tmp}" "${in_f}"

# removing previously inserted leading 0s from the var name
sed 's/_0\+\([1-9][0-9]*\):/_\1:/g' "${in_f}" > "${tmp}"
mv "${tmp}" "${in_f}"
