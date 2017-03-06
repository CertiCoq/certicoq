type tree = Leaf | Node of int * tree * tree

let rec insert (key: int) (t: tree) : tree =
 match t with
  Leaf -> Node(key,Leaf,Leaf)
 | Node(k,left,right) ->
    if (key<k) then Node(k, insert key left, right)
    else if (k<key) then Node (k, left, insert key right)
    else t

let rec build (n: int) (t: tree) : tree =
 if n>0 then build (n-1) (insert (Random.int 1000) t)
 else t

let rec measure (t: tree) : int =
 match t with Leaf -> 0 
            | Node (_,left,right) -> 1 + measure left + measure right

let () =
  let n = int_of_string (Sys.argv.(1)) in
  let t = build n Leaf in
  let s = measure t in
  (print_string "Tree has "; print_int s; print_string "nodes\n")


  
