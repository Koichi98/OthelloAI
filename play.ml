open Array
open Color
open Command


type board = color array array
type hand = Hand of int * int * int 

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
  (board.(i).(j) = none) && is_effective board color (i,j)


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
  List.filter (is_valid_move board color)
    (mix ls ls)

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
(*勝ち筋が多いほうで進む*)
(*最小の石数が最大なほうに進む*)

let judge board color win whole= (*どちらが勝ったか*)
  let n = count board color in
  let ocolor = opposite_color color in
  let m = count board ocolor in
  (if n>=m then 
    (win+.1.,whole+.1.)
  else 
    (win,whole+.1.))

let copy_board board =  (*盤面のコピーをとる*)
  let new_board = Array.make_matrix 10 10 none in
    for i=0 to 9 do
      for j=0 to 9 do
        new_board.(i).(j) <- board.(i).(j);
      done;
    done;
  new_board

let rec mating_check hand board cur_color my_color win whole= 
      let (i,j) = hand in
      let new_board = doMove board (Mv(i,j)) cur_color in
      let ocolor = opposite_color cur_color in
      if (count_step new_board) = 64 then 
        judge new_board my_color win whole
      else
        let new_ms = valid_moves new_board ocolor in
          (if new_ms = [] then (*ocolorがパスの時*)
          let ms = valid_moves new_board cur_color in
            (if ms = [] then (*cur_colorもパスの時*)
              judge new_board my_color win whole
            else 
              mating_sub ms new_board cur_color my_color win whole)
          else
          mating_sub new_ms new_board ocolor my_color win whole)
and mating_sub ms board cur_color my_color win whole=
    match ms with
    |[] -> (win,whole)
    |(i,j)::rest -> 
      let new_board = copy_board board in
      let (new_win,new_whole) = mating_check (i,j) new_board cur_color my_color win whole in
      mating_sub rest board cur_color my_color new_win new_whole

let rec mating board color ms= (*読み切りを行う,勝つ確率の最も高い手の方向に進む.*) 
    match ms with
    |[] -> []
    |(i,j)::rest -> 
      let new_board = copy_board board in
      let (win,whole) = mating_check (i,j) new_board color color 0. 0. in 
      let p = win /. whole in
      (p,(i,j))::(mating board color rest)

let rec print_p_ls ls =
  match ls with 
  |[] -> ()
  |(p,(i,j))::rest -> 
    Printf.printf "( %f" p; Printf.printf ",";Printf.printf "(%d" i; Printf.printf ",%d" j; Printf.printf ")"; Printf.printf ")  ";print_p_ls rest

let rec choose_max ls max= (*(p:確率,(手))を並べたリストの中でpが最も大きい手を選択しする.*)
  let (p',(i',j')) = max in
  match ls with
  |[] -> (i',j')
  |(p,(i,j))::rest -> 
    if p > p' then 
      choose_max rest (p,(i,j))
    else 
      choose_max rest max

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

let play board color =
  (*print_board board;*)(*盤面の出力*)
  let ms = valid_moves board color in
  (*print_valid_moves ms;*) (*合法手の出力*)
    if ms = [] then
      Pass
    else
      let step = count_step board in 
      (if step < 55 then  
        let k = Random.int (List.length ms) in
        let (i,j) = List.nth ms k in
        Mv (i,j)
      else 
        let new_board = copy_board board in
        let ls = mating new_board color ms in
        let def::rest = ls in
        let (i,j) = choose_max ls def in
        (*print_p_ls ls; *)
        Mv (i,j))



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
