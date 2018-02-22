in_f="${0}"
tmp="${in_f}1"

# get rid of "() Bool" adding trailing "  :  "
sed 's/ () Bool/  :  /g' "${in_f}"  > "${tmp}" 
mv "${tmp}"  "${in_f}" 
# get rid of "(() (_ BitVec \d+))" adding trailing "  :  "
sed 's/ () (_ BitVec [[:digit:]]\+)/  :  /g' "${in_f}"  > "${tmp}" 
mv "${tmp}"  "${in_f}"
# get rid of "  (define-fun " 
sed 's/  (define-fun //g' "${in_f}"  > "${tmp}" 
mv "${tmp}"  "${in_f}" 

# fixing leading 0 in var indexes
sed 's/\([^ ]\+\)_\([0-9]  \)/\1_000\2/g' "${in_f}"  > "${tmp}" 
mv "${tmp}"  "${in_f}" 
sed 's/\([^ ]\+\)_\([0-9][0-9]  \)/\1_00\2/g' "${in_f}"  > "${tmp}" 
mv "${tmp}"  "${in_f}" 
sed 's/\([^ ]\+\)_\([0-9][0-9][0-9]  \)/\1_0\2/g' "${in_f}"  > "${tmp}" 
mv "${tmp}"  "${in_f}" 
# copying indices before variable names
sed 's/\([^ ]\+\)_\([0-9][0-9][0-9][0-9]\)  /\2: \1_\2  /g' "${in_f}"  > "${tmp}" 
mv "${tmp}"  "${in_f}" 

# fixing leading 0 in |comment| indexes
sed 's/|\([^|]\+\)_\([0-9]|  \)/|\1_000\2/g' "${in_f}"  > "${tmp}" 
mv "${tmp}"  "${in_f}" 
sed 's/|\([^|]\+\)_\([0-9][0-9]|  \)/|\1_00\2/g' "${in_f}"  > "${tmp}" 
mv "${tmp}"  "${in_f}" 
sed 's/|\([^|]\+\)_\([0-9][0-9][0-9]|  \)/|\1_0\2/g' "${in_f}"  > "${tmp}" 
mv "${tmp}"  "${in_f}" 
# copying indices before variable names
sed 's/|\([^|]\+\)_\([0-9][0-9][0-9][0-9]\)|  /\2: |\1_\2|  /g' "${in_f}"  > "${tmp}" 
mv "${tmp}"  "${in_f}" 

# removing new_line beween var and value
sed ':a;N;$!ba;s/  :  \n    /: /g' "${in_f}"  > "${tmp}" 
mv "${tmp}"  "${in_f}" 

# removing last )
sed 's/.$//' "${in_f}"  > "${tmp}" 
mv "${tmp}"  "${in_f}" 
# sed 's/(model$//' "${in_f}"  > "${tmp}" 
# mv "${tmp}"  "${in_f}" 
# sed 's/sat$//' "${in_f}"  > "${tmp}" 
# mv "${tmp}"  "${in_f}" 

# sorting the file
sort "${in_f}"  > "${tmp}" 
mv "${tmp}"  "${in_f}" 
