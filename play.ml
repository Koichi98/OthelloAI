open Array
open Color
open Command
(*open Board*)


let init_board () =
  let board = Array.make_matrix 10 10 none in
    for i=0 to 9 do
      board.(i).(0) <- sentinel ;
      board.(i).(9) <- sentinel ;
      board.(0).(i) <- sentinel ;
      board.(9).(i) <- sentinel ;
    done;
    board.(4).(4) <- white;
    board.(5).(5) <- white;
    board.(4).(5) <- black;
    board.(5).(4) <- black;
    board

let dirs = [ (-1,-1); (0,-1); (1,-1); (-1,0); (1,0); (-1,1); (0,1); (1,1) ]

let flippable_indices_line board color (di,dj) (i,j) =
  let ocolor = opposite_color color in
  let rec f (di,dj) (i,j) r =
    if board.(i).(j) = ocolor then
      g (di,dj) (i+di,j+dj) ( (i,j) :: r )
    else
      []
  and    g (di,dj) (i,j) r =
    if board.(i).(j) = ocolor then
      g (di,dj) (i+di,j+dj) ( (i,j) :: r )
    else if board.(i).(j) = color then
      r
    else
      [] in
      f (di,dj) (i,j) []

let flippable_indices board color (i,j) =
  let bs = List.map (fun (di,dj) -> flippable_indices_line board color (di,dj) (i+di,j+dj)) dirs in
    List.concat bs

let is_effective board color (i,j) =
  match flippable_indices board color (i,j) with
      [] -> false
    | _  -> true

let is_valid_move board color (i,j) =
  board.(i).(j) = none && is_effective board color (i,j)

let is_none board (i,j) = 
  if board.(i).(j) = none then 
    true
  else 
    false

let doMove board com color =
  match com with
      GiveUp  -> board
    | Pass    -> board
    | Mv (i,j) ->
	let ms = flippable_indices board color (i,j) in
	let _  = List.map (fun (ii,jj) -> board.(ii).(jj) <- color) ms in
	let _  = board.(i).(j) <- color in
	  board

let mix xs ys =
  List.concat (List.map (fun x -> List.map (fun y -> (x,y)) ys) xs)

let valid_moves board color =
  let ls = [1;2;3;4;5;6;7;8] in
  let none_ls = List.filter (is_none board) (mix ls ls) in
  List.filter (is_effective board color) none_ls

let rec print_valid_moves ms = 
  match ms with 
  |[] -> ()
  |(i,j)::rest -> Printf.printf "(%d" i; Printf.printf ",%d" j; Printf.printf ")  ";print_valid_moves rest

let rec count_step board = (*何手目が終了した状態か*)
  let r = ref 0 in
    for i=1 to 8 do
      for j=1 to 8 do
        if board.(i).(j) = white || board.(i).(j) = black then r := !r + 1
      done
    done;
    !r

let count board color =
  let s = ref 0 in
    for i=1 to 8 do
      for j=1 to 8 do
        if board.(i).(j) = color then s := !s + 1
      done
    done;
    !s


let copy_board board =  (*盤面のコピーをとる*)
  let new_board = Array.make_matrix 10 10 none in
    for i=0 to 9 do
      for j=0 to 9 do
        new_board.(i).(j) <- board.(i).(j);
      done;
    done;
  new_board


(*move_ordering:相手の手数が少なくなる手から探索を始めるために有効手のリストをソート*)
let rec move_ordering_sub (i,j) board color = 
      let copied_board = copy_board board in
      let moved_board = doMove copied_board (Mv(i,j)) color in
      let ocolor = opposite_color color in
      let oms = valid_moves moved_board ocolor in 
      List.length oms
  
let rec ordering_sort factor ls =
  match ls with
  |[] -> [factor]
  |(k,(i,j))::rest ->
    let (key,(i',j')) = factor in
    if key > k then 
      (k,(i,j))::(ordering_sort factor rest)
    else
      factor::(k,(i,j))::rest 
  
let rec move_ordering_before_arranged ms board color ls = 
  match ms with
  |[] -> ls
  |(i,j)::rest -> 
    let key = move_ordering_sub (i,j) board color in
    let sorted_ls = ordering_sort (key,(i,j)) ls in
    move_ordering_before_arranged rest board color sorted_ls

let rec move_ordering ls = 
  match ls with
  |[] -> []
  |(k,(i,j))::rest -> 
    (i,j)::(move_ordering rest)

let flag = ref 0
let node = ref 0

(*完全読み切り 必勝必敗プログラム node<1000*)
let rec win_sub_rtd board color ms =  (*自分が一手進めたある局面で自分の必勝が成立するならば(true,(手)),成立しないならば(false,(手)).*)
  match ms with 
  |[] -> (false,(0,0))
  |(i,j)::rest -> 
    let copied_board = copy_board board in
    let moved_board = doMove copied_board (Mv(i,j)) color in
    let ocolor = opposite_color color in
    (match lose_rtd moved_board ocolor with
    |(true,(i',j')) -> (true,(i,j))
    |(false,(i',j')) -> 
      win_sub_rtd board color rest)
and win_rtd board color = 
  let ms = valid_moves board color in
  let ocolor = opposite_color color in
  let oms = valid_moves board ocolor in
  let c = count board color in
  let oc = count board ocolor in  
  node:=!node+1;
  if !node > 75000 then
    (false,(0,0))
  else if (ms=[] && oms = []) then (*終局している*)
    if (c>oc) then (*自分が既に勝っている*)
    (true,(0,0))
    else 
    (false,(0,0))
  else if ms = [] then(*終局していない&&自分がパス*)
    match lose_rtd board ocolor with
    |(true,(i',j')) -> (true,(0,0))
    |(false,(i',j')) -> (false,(0,0))
  else(*終局していない&&自分がパスしない*)
    (*if !flag = 0 then (*探索木の一番上*)
      let ordered_ms = move_ordering_before_arranged ms board color [] in
      let arranged_ms = move_ordering ordered_ms in
      flag := 1;win_sub board color arranged_ms (*必勝手筋があるかどうか*)
    else*)
      win_sub_rtd board color ms (*必勝手筋があるかどうか*)
and lose_sub_rtd board color ms =
  match ms with
  |[] -> (true,(0,0))
  |(i,j)::rest ->
    let copied_board = copy_board board in
    let moved_board = doMove copied_board (Mv(i,j)) color in
    let ocolor = opposite_color color in
    (match win_rtd moved_board ocolor with 
    |(false,(i',j')) -> (false,(i,j))
    |(true,(i',j')) -> 
      lose_sub_rtd board color rest)
and lose_rtd board color = 
  let ms = valid_moves board color in
  let ocolor = opposite_color color in
  let oms = valid_moves board ocolor in
  let c = count board color in
  let oc = count board ocolor in
    node:=!node+1;
  if !node > 75000 then
    (false,(0,0))
  else if (ms=[] && oms = []) then (*終局している*)  
    if (oc>c) then (*相手が既に勝っている*)
      (true,(0,0))
    else 
      (false,(0,0))
  else if ms=[] then(*終局してない&&自分がパス*)
    match win_rtd board ocolor with
    |(true,(i',j')) -> (true,(0,0))
    |(false,(i',j')) -> (false,(0,0))
  else(*終局していない&&自分がパスしない*)
    lose_sub_rtd board color ms


(*完全読み切り 必勝必敗プログラム*)
let rec win_sub board color ms =  (*自分が一手進めたある局面で自分の必勝が成立するならば(true,(手)),成立しないならば(false,(手)).*)
  match ms with 
  |[] -> (false,(0,0))
  |(i,j)::rest -> 
    let copied_board = copy_board board in
    let moved_board = doMove copied_board (Mv(i,j)) color in
    let ocolor = opposite_color color in
    (match lose moved_board ocolor with
    |(true,(i',j')) -> (true,(i,j))
    |(false,(i',j')) -> 
      win_sub board color rest)
and win board color = 
  let ms = valid_moves board color in
  let ocolor = opposite_color color in
  let oms = valid_moves board ocolor in
  let c = count board color in
  let oc = count board ocolor in  
  if (ms=[] && oms = []) then (*終局している*)
    if (c>oc) then (*自分が既に勝っている*)
    (true,(0,0))
    else 
    (false,(0,0))
  else if ms = [] then(*終局していない&&自分がパス*)
    match lose board ocolor with
    |(true,(i',j')) -> (true,(0,0))
    |(false,(i',j')) -> (false,(0,0))
  else(*終局していない&&自分がパスしない*)
    (*if !flag = 0 then (*探索木の一番上*)
      let ordered_ms = move_ordering_before_arranged ms board color [] in
      let arranged_ms = move_ordering ordered_ms in
      flag := 1;win_sub board color arranged_ms (*必勝手筋があるかどうか*)
    else*)
      win_sub board color ms (*必勝手筋があるかどうか*)
and lose_sub board color ms =
  match ms with
  |[] -> (true,(0,0))
  |(i,j)::rest ->
    let copied_board = copy_board board in
    let moved_board = doMove copied_board (Mv(i,j)) color in
    let ocolor = opposite_color color in
    (match win moved_board ocolor with 
    |(false,(i',j')) -> (false,(i,j))
    |(true,(i',j')) -> 
      lose_sub board color rest)
and lose board color = 
  let ms = valid_moves board color in
  let ocolor = opposite_color color in
  let oms = valid_moves board ocolor in
  let c = count board color in
  let oc = count board ocolor in
  if (ms=[] && oms = []) then (*終局している*)  
    if (oc>c) then (*相手が既に勝っている*)
      (true,(0,0))
    else 
      (false,(0,0))
  else if ms=[] then(*終局してない&&自分がパス*)
    match win board ocolor with
    |(true,(i',j')) -> (true,(0,0))
    |(false,(i',j')) -> (false,(0,0))
  else(*終局していない&&自分がパスしない*)
    lose_sub board color ms

    
let mycolor color mcolor = 
  let ocolor = opposite_color color in
  if color = mcolor then 
  1 
  else if color = ocolor then
  -1 
  else 
  0

let eval board color =  (*盤面の各マスに点数を割り振って盤面を評価*)
  let board_point =  
    30*(mycolor board.(1).(1) color)+ (-12)*(mycolor board.(1).(2) color)+ 0*(mycolor board.(1).(3) color)+ (-1)*(mycolor board.(1).(4) color)+ (-1)*(mycolor board.(1).(5) color)+ 0*(mycolor board.(1).(6) color)+ (-12)*(mycolor board.(1).(7) color)+ 30*(mycolor board.(1).(8) color)+
    (-12)*(mycolor board.(2).(1) color)+ (-15)*(mycolor board.(2).(2) color)+ (-3)*(mycolor board.(2).(3) color)+ (-3)*(mycolor board.(2).(4) color)+ (-3)*(mycolor board.(2).(5) color)+ (-3)*(mycolor board.(2).(6) color)+ (-15)*(mycolor board.(2).(7) color)+ (-12)*(mycolor board.(2).(8) color)+
    0*(mycolor board.(3).(1) color)+ (-3)*(mycolor board.(3).(2) color)+ 0*(mycolor board.(3).(3) color)+ (-1)*(mycolor board.(3).(4) color)+ (-1)*(mycolor board.(3).(5) color)+ 0*(mycolor board.(3).(6) color)+ (-3)*(mycolor board.(3).(7) color)+ 0*(mycolor board.(3).(8) color)+
    (-1)*(mycolor board.(4).(1) color)+ (-3)*(mycolor board.(4).(2) color)+ (-1)*(mycolor board.(4).(3) color)+ (-1)*(mycolor board.(4).(4) color)+ (-1)*(mycolor board.(4).(5) color)+ (-1)*(mycolor board.(4).(6) color)+ (-3)*(mycolor board.(4).(7) color)+ (-1)*(mycolor board.(4).(8) color)+
    (-1)*(mycolor board.(5).(1) color)+ (-3)*(mycolor board.(5).(2) color)+ (-1)*(mycolor board.(5).(3) color)+ (-1)*(mycolor board.(5).(4) color)+ (-1)*(mycolor board.(5).(5) color)+ (-1)*(mycolor board.(5).(6) color)+ (-3)*(mycolor board.(5).(7) color)+ (-1)*(mycolor board.(5).(8) color)+
    0*(mycolor board.(6).(1) color)+ (-3)*(mycolor board.(6).(2) color)+ 0*(mycolor board.(6).(3) color)+ (-1)*(mycolor board.(6).(4) color)+ (-1)*(mycolor board.(6).(5) color)+ 0*(mycolor board.(6).(6) color)+ (-3)*(mycolor board.(6).(7) color)+ 0*(mycolor board.(6).(8) color)+
    (-12)*(mycolor board.(7).(1) color)+ (-15)*(mycolor board.(7).(2) color)+ (-3)*(mycolor board.(7).(3) color)+ (-3)*(mycolor board.(7).(4) color)+ (-3)*(mycolor board.(7).(5) color)+ (-3)*(mycolor board.(7).(6) color)+ (-15)*(mycolor board.(7).(7) color)+ (-12)*(mycolor board.(7).(8) color)+
    30*(mycolor board.(8).(1) color)+ (-12)*(mycolor board.(8).(2) color)+ 0*(mycolor board.(8).(3) color)+ (-1)*(mycolor board.(8).(4) color)+ (-1)*(mycolor board.(8).(5) color)+ 0*(mycolor board.(8).(6) color)+ (-12)*(mycolor board.(8).(7) color)+ 30*(mycolor board.(8).(8) color)
    in
  let ms = valid_moves board color in 
  let validity_point = List.length ms in
    board_point + validity_point

(*Negamax探索法*)
let rec negamax board color depth =  
  if depth = 0 then 
  let ocolor = opposite_color color in
  (*let c = count board ocolor in (*単純な自分の石の個数でdepth手後の盤面を評価*)*)
  let c = eval board ocolor in
  (c,(0,0))
  else
    let ms = valid_moves board color in 
    if ms=[] then 
      let ocolor = opposite_color color in
      negamax board ocolor (depth-1) 
    else
      negamax_sub board color depth ms (-10000,(0,0))
and negamax_sub board color depth ms max =
    match ms with
    |[] -> 
     let (m,(i,j)) = max in
      (-m,(i,j))
    |(i,j)::rest ->
      let copied_board = copy_board board in
      let moved_board = doMove copied_board (Mv(i,j)) color in
      let ocolor = opposite_color color in
      let (m,(i',j')) = max in
      let (v,(k,l)) = negamax moved_board ocolor (depth-1) in
      if v > m then 
        negamax_sub board color depth rest (v,(i,j))
      else 
        negamax_sub board color depth rest max

(*Negaalpha探索法*) 
let rec negaalpha board color depth alpha beta =  (*最初はalpha:-大きい,beta:-大きいで呼ぶ*)
  if depth = 0 then 
  let ocolor = opposite_color color in
  let c = eval board ocolor in
  (c,(0,0))
  else
    let ms = valid_moves board color in 
    if depth > 3  then
      if ms=[] then 
        let ocolor = opposite_color color in
        negaalpha board ocolor (depth-1) (-alpha) (-beta)
      else
        let ordered_ms = move_ordering_before_arranged ms board color [] in
        let arranged_ms = move_ordering ordered_ms in
        negaalpha_sub board color depth arranged_ms (-10000,(0,0)) alpha beta
    else
      if ms=[] then 
        let ocolor = opposite_color color in
        negaalpha board ocolor (depth-1) alpha beta
      else
        negaalpha_sub board color depth ms (-10000,(0,0)) alpha beta
and negaalpha_sub board color depth ms max alpha beta=
    match ms with
    |[] -> 
     let (m,(i,j)) = max in
      (-m,(i,j))
    |(i,j)::rest ->
      let copied_board = copy_board board in
      let moved_board = doMove copied_board (Mv(i,j)) color in
      let ocolor = opposite_color color in
      let (m,(i',j')) = max in
      let (v,(k',l')) = negaalpha moved_board ocolor (depth-1) alpha beta in
      if depth mod 2 = 1 then (*奇数回潜ることを前提*)
        if alpha > (-v) then 
            (-v,(i,j))
        else
          if v > m then 
            negaalpha_sub board color depth rest (v,(i,j)) alpha v 
          else 
            negaalpha_sub board color depth rest max alpha m  
      else
        if beta > (-v) then 
            (-v,(i,j))
        else
          if v > m then 
            negaalpha_sub board color depth rest (v,(i,j)) v beta
          else 
            negaalpha_sub board color depth rest max v beta

let print_board board =
print_endline " |A B C D E F G H ";
print_endline "-+----------------";
for j=1 to 8 do
  print_int j; print_string "|";
  for i=1 to 8 do
    print_color (board.(i).(j)); print_string " "
  done;
  print_endline ""
done;
print_endline "  (X: Black,  O: White)"

let file = "logbook.gam"

type opmove = PMove of move | OMove of move

let string_of_move1 = function
  | Pass   -> "PASS"
  | GiveUp -> "GIVEUP"
  | Mv (i,j) ->
    let ci = char_of_int (i + int_of_char 'a' - 1) in
    let cj = char_of_int (j + int_of_char '1' - 1) in
    let s  = Bytes.make 2 ' ' in
    let _  = ( Bytes.set s 0 ci; Bytes.set s 1 cj) in
    Bytes.to_string s

let string_of_opmove = function
  | PMove mv -> "+" ^ string_of_move1 mv
  | OMove mv -> "-" ^ string_of_move1 mv

type hist = opmove list

let string_of_hist x = List.fold_left (fun r a -> string_of_opmove a ^ " " ^ r) "" x
let print_hist x = print_endline (string_of_hist x)

let board_spin = ref 0

let rec trans_hist hist str = 
  match !board_spin with
  |0 ->
    (match hist with
    |[] -> str
    |PMove(Mv(i,j))::rest
      ->
      let ci = char_of_int (i + int_of_char 'a' - 1) in
      let cj = char_of_int (j + int_of_char '1' - 1) in
      let s  = Bytes.make 2 ' ' in
      let _  = ( Bytes.set s 0 ci; Bytes.set s 1 cj) in
      trans_hist rest (s^str)
    |OMove(Mv(i,j))::rest
      ->
      let ci = char_of_int (i + int_of_char 'a' - 1) in
      let cj = char_of_int (j + int_of_char '1' - 1) in
      let s  = Bytes.make 2 ' ' in
      let _  = ( Bytes.set s 0 ci; Bytes.set s 1 cj) in
      trans_hist rest (s^str)
    |_ -> "NONE")
  |1 ->
    (match hist with
    |[] -> str
    |PMove(Mv(i,j))::rest
      ->
      let ci = char_of_int (j + int_of_char 'a' - 1) in
      let cj = char_of_int (i + int_of_char '1' - 1) in
      let s  = Bytes.make 2 ' ' in
      let _  = ( Bytes.set s 0 ci; Bytes.set s 1 cj) in
      trans_hist rest (s^str)
    |OMove(Mv(i,j))::rest
      ->
      let ci = char_of_int (j + int_of_char 'a' - 1) in
      let cj = char_of_int (i + int_of_char '1' - 1) in
      let s  = Bytes.make 2 ' ' in
      let _  = ( Bytes.set s 0 ci; Bytes.set s 1 cj) in
      trans_hist rest (s^str)
    |_ -> "NONE")
  |2 ->
    (match hist with
    |[] -> str
    |PMove(Mv(i,j))::rest
      ->
      let ci = char_of_int (9-j + int_of_char 'a' - 1) in
      let cj = char_of_int (9-i + int_of_char '1' - 1) in
      let s  = Bytes.make 2 ' ' in
      let _  = ( Bytes.set s 0 ci; Bytes.set s 1 cj) in
      trans_hist rest (s^str)
    |OMove(Mv(i,j))::rest
      ->
      let ci = char_of_int (9-j + int_of_char 'a' - 1) in
      let cj = char_of_int (9-i + int_of_char '1' - 1) in
      let s  = Bytes.make 2 ' ' in
      let _  = ( Bytes.set s 0 ci; Bytes.set s 1 cj) in
      trans_hist rest (s^str)
    |_ -> "NONE")
  |3 ->
    (match hist with
    |[] -> str
    |PMove(Mv(i,j))::rest
      ->
      let ci = char_of_int (9-i + int_of_char 'a' - 1) in
      let cj = char_of_int (9-j + int_of_char '1' - 1) in
      let s  = Bytes.make 2 ' ' in
      let _  = ( Bytes.set s 0 ci; Bytes.set s 1 cj) in
      trans_hist rest (s^str)
    |OMove(Mv(i,j))::rest
      ->
      let ci = char_of_int (9-i + int_of_char 'a' - 1) in
      let cj = char_of_int (9-j + int_of_char '1' - 1) in
      let s  = Bytes.make 2 ' ' in
      let _  = ( Bytes.set s 0 ci; Bytes.set s 1 cj) in
      trans_hist rest (s^str)
    |_ -> "NONE")


let spin hist =
  let OMove(Mv(i,j))::rest = hist in
  let ci = char_of_int (i + int_of_char 'a' - 1) in
  let cj = char_of_int (j + int_of_char '1' - 1) in
  let s  = Bytes.make 2 ' ' in
  let _  = ( Bytes.set s 0 ci; Bytes.set s 1 cj) in
    match s with
    |"d3" -> ()
    |"c4" -> board_spin:=1;()
    |"f5" -> board_spin:=2;()
    |"e6" -> board_spin:=3;()

let turn_back hand = 
  match (!board_spin) with
  |0 -> hand 
  |1 -> let (i,j) = hand in (j,i)
  |2 -> let (i,j) = hand in (9-j,9-i)
  |3 -> let (i,j) = hand in (9-i,9-j)


let rec trans_next nexty nextx =
    let i = (int_of_char nexty) - (int_of_char 'a') + 1 in
    let j = (int_of_char nextx) - (int_of_char '1') + 1 in
    turn_back (i,j)

let x = ref 'a'
let y = ref '0'

let rec strcmp str ic step board color =
    for i=1 to 11833 do
      let line = input_line ic in
      let str2 = String.sub line 0 ((step-5)*2) in
      if str = ("d3"^str2) then 
        let nextx = String.get line ((step-5)*2+1) in
        let nexty = String.get line ((step-5)*2) in
        x:=nextx;y:=nexty;
        ()
      else
        ()
    done;
    if !x = 'a' && !y = '0' then
      let (m,(i,j)) = negaalpha board color 5 (-10000) (-10000) in 
      (i,j)
    else
        trans_next (!y) (!x)
      

let rec early_stage hist ic step board color = 
  let str = trans_hist hist "" in
    strcmp str ic step board color

let play board color hist =
  (*print_board board;(*盤面の出力*)*)
  (*print_hist hist;*)
  let step = count_step board in 
  let ms = valid_moves board color in
  (*print_valid_moves ms;*) (*合法手の出力*)
      Printf.printf "%d\n" step;
      x := 'a';y:='0';
    if ms = [] then
      Pass
    else
      if step = 4 then 
        let i = (int_of_char 'd') - (int_of_char 'a') + 1 in
        let j = (int_of_char '3') - (int_of_char '1') + 1 in
        Mv(i,j)
      else if step = 5 then
        let ic = open_in file in
        let (i,j) = spin hist;early_stage hist ic step board color in
        close_in ic;
        Mv (i,j)
      else if step < 23 then
        let ic = open_in file in
        let (i,j) = early_stage hist ic step board color in
        close_in ic;
        Mv (i,j)
      else if step < 41 then 
        let (m,(i,j)) = negaalpha board color 5 (-10000) (-10000) in 
        Mv (i,j)
      else if step < 52 then
        match win_rtd board color with
        |(true,(i,j)) -> (*必勝手筋があった場合*)
        Printf.printf "必勝\n";
          node:=0;Mv (i,j)
        |(false,(i,j)) ->(*必勝がなかった場合*)
          let (m,(i,j)) = negaalpha board color 5 (-10000) (-10000) in 
          Printf.printf "必勝なし\n";
          node:=0;Mv (i,j)
      else
        match win board color with
        |(true,(i,j)) -> (*必勝手筋があった場合*)
        Printf.printf "必勝\n";
          node:=0;Mv (i,j)
        |(false,(i,j)) ->(*必勝がなかった場合*)
         Printf.printf "必勝なし\n";
          let k = Random.int (List.length ms) in
          let (i,j) = List.nth ms k in
          node:=0;Mv (i,j)



let report_result board =
  let _ = print_endline "========== Final Result ==========" in
  let bc = count board black in
  let wc = count board white in
    if bc > wc then
      print_endline "*Black wins!*"
    else if bc < wc then
      print_endline "*White wins!*"
    else
      print_endline "*Even*";
    print_string "Black: "; print_endline (string_of_int bc);
    print_string "White: "; print_endline (string_of_int wc);
    print_board board
