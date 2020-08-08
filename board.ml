open Int64

type board = int64 * int64

let init_board1 () =
  let w = 68853694464L in
  let b = 34628173824L in
  let board = (w,b) in
    board

let rec makeLegalBoard_sub board = 
  let (mboard,oboard) = board in
  let horizontalWatchBoard = logand oboard 9114861777597660798L in
  let verticalWatchBoard = logand oboard 72057594037927680L in
  let allSideWatchBoard = logand oboard 35604928818740736L in
  let blankBoard = lognot (logor mboard oboard) in
  let legalBoard = ref 0L in
  (*左*)
  let tmp = ref (logand horizontalWatchBoard (shift_left mboard 1)) in
  tmp := logor (!tmp) (logand horizontalWatchBoard (shift_left !tmp 1));
  tmp := logor (!tmp) (logand horizontalWatchBoard (shift_left !tmp 1));
  tmp := logor (!tmp) (logand horizontalWatchBoard (shift_left !tmp 1));
  tmp := logor (!tmp) (logand horizontalWatchBoard (shift_left !tmp 1));
  tmp := logor (!tmp) (logand horizontalWatchBoard (shift_left !tmp 1));
  legalBoard := logor !legalBoard (logand blankBoard (shift_left !tmp 1));
  (*右*)
  tmp := logand horizontalWatchBoard (shift_right mboard 1);
  tmp := logor (!tmp) (logand horizontalWatchBoard (shift_right !tmp 1));
  tmp := logor (!tmp) (logand horizontalWatchBoard (shift_right !tmp 1));
  tmp := logor (!tmp) (logand horizontalWatchBoard (shift_right !tmp 1));
  tmp := logor (!tmp) (logand horizontalWatchBoard (shift_right !tmp 1));
  tmp := logor (!tmp) (logand horizontalWatchBoard (shift_right !tmp 1));
  legalBoard := logor !legalBoard (logand blankBoard (shift_right !tmp 1));
  (*上*)
  tmp := logand verticalWatchBoard (shift_left mboard 8);
  tmp := logor (!tmp) (logand verticalWatchBoard (shift_left !tmp 8));
  tmp := logor (!tmp) (logand verticalWatchBoard (shift_left !tmp 8));
  tmp := logor (!tmp) (logand verticalWatchBoard (shift_left !tmp 8));
  tmp := logor (!tmp) (logand verticalWatchBoard (shift_left !tmp 8));
  tmp := logor (!tmp) (logand verticalWatchBoard (shift_left !tmp 8));
  legalBoard := logor !legalBoard (logand blankBoard (shift_left !tmp 8));
  (*下*)
  tmp := logand verticalWatchBoard (shift_right mboard 8);
  tmp := logor (!tmp) (logand verticalWatchBoard (shift_right !tmp 8));
  tmp := logor (!tmp) (logand verticalWatchBoard (shift_right !tmp 8));
  tmp := logor (!tmp) (logand verticalWatchBoard (shift_right !tmp 8));
  tmp := logor (!tmp) (logand verticalWatchBoard (shift_right !tmp 8));
  tmp := logor (!tmp) (logand verticalWatchBoard (shift_right !tmp 8));
  legalBoard := logor !legalBoard (logand blankBoard (shift_right !tmp 8));
  (*右斜め上*)
  tmp := logand allSideWatchBoard (shift_left mboard 7);
  tmp := logor (!tmp) (logand allSideWatchBoard (shift_left !tmp 7));
  tmp := logor (!tmp) (logand allSideWatchBoard (shift_left !tmp 7));
  tmp := logor (!tmp) (logand allSideWatchBoard (shift_left !tmp 7));
  tmp := logor (!tmp) (logand allSideWatchBoard (shift_left !tmp 7));
  tmp := logor (!tmp) (logand allSideWatchBoard (shift_left !tmp 7));
  legalBoard := logor !legalBoard (logand blankBoard (shift_left !tmp 7));
  (*左斜め上*)
  tmp := logand allSideWatchBoard (shift_left mboard 9);
  tmp := logor (!tmp) (logand allSideWatchBoard (shift_left !tmp 9));
  tmp := logor (!tmp) (logand allSideWatchBoard (shift_left !tmp 9));
  tmp := logor (!tmp) (logand allSideWatchBoard (shift_left !tmp 9));
  tmp := logor (!tmp) (logand allSideWatchBoard (shift_left !tmp 9));
  tmp := logor (!tmp) (logand allSideWatchBoard (shift_left !tmp 9));
  legalBoard := logor !legalBoard (logand blankBoard (shift_left !tmp 9));
  (*右斜め下*)
  tmp := logand allSideWatchBoard (shift_right mboard 9);
  tmp := logor (!tmp) (logand allSideWatchBoard (shift_right !tmp 9));
  tmp := logor (!tmp) (logand allSideWatchBoard (shift_right !tmp 9));
  tmp := logor (!tmp) (logand allSideWatchBoard (shift_right !tmp 9));
  tmp := logor (!tmp) (logand allSideWatchBoard (shift_right !tmp 9));
  tmp := logor (!tmp) (logand allSideWatchBoard (shift_right !tmp 9));
  legalBoard := logor !legalBoard (logand blankBoard (shift_right !tmp 9));
  (*左斜め下*)
  tmp := logand allSideWatchBoard (shift_right mboard 7);
  tmp := logor (!tmp) (logand allSideWatchBoard (shift_right !tmp 7));
  tmp := logor (!tmp) (logand allSideWatchBoard (shift_right !tmp 7));
  tmp := logor (!tmp) (logand allSideWatchBoard (shift_right !tmp 7));
  tmp := logor (!tmp) (logand allSideWatchBoard (shift_right !tmp 7));
  tmp := logor (!tmp) (logand allSideWatchBoard (shift_right !tmp 7));
  legalBoard := logor !legalBoard (logand blankBoard (shift_right !tmp 7));
  !legalBoard

let makeLegalBoard board color =
  let (w,b) = board in
  if color = white then 
    makeLegalBoard_sub (w,b) 
  else 
    makeLegalBoard_sub (b,w) 

let rec valid_moves1_sub legalBoard n= 
  if n = 0 then
    []
  else
    if legalBoard land -4611686018427387904 = -4611686018427387904 then (*符号付63ビット整数の最上位ビットが1*)
      (8 - (n mod 8) + 1,8 - (n / 8))::(valid_moves1_sub (legalBoard lsl 1) (n-1))
    else
      valid_moves1_sub (legalBoard lsl 1) (n-1)
  
let valid_moves1 board color = 
  let legalBoard = makeLegalBoard board color in
  if (logand legalBoard (-9223372036854775808L)) = -9223372036854775808L then (*最上位ビットだけ確認し,int型に直して検証*)
    (1,1)::(valid_moves1_sub (to_int legalBoard) 63) 
  else
    valid_moves1_sub (to_int legalBoard) 63
    


let rec transfer put k = 
  match k with
  |0 -> logand (shift_left put 8) (-256L)
  |1 -> logand (shift_left put 7) 9187201950435737344L
  |2 -> logand (shift_right put 1) 9187201950435737471L
  |3 -> logand (shift_right put 9) 35887507618889599L
  |4 -> logand (shift_right put 8) 72057594037927935L
  |5 -> logand (shift_right put 7) 71775015237779198L
  |6 -> logand (shift_left put 1) (-72340172838076674L)
  |7 -> logand (shift_left put 9) (-72340172838076928L)
  |_ -> 0L

let rec reverse_loop mask board k rev_ rev =
  let (mboard,oboard) = board in
  if (mask != 0L) && ((logand mask oboard)!= 0L) then
    let rev_' = logor rev_ mask in
    let mask' = transfer mask k in
    print_int k;
    reverse_loop mask' board k rev_' rev
  else 
    if (logand mask mboard != 0L) then
      logor rev rev_
    else 
      rev

let rec reverse_sub put board k rev=
  let mask = transfer put k in
  if k=7 then
    reverse_loop mask board k 0L rev
  else
    reverse_sub put board (k+1) (reverse_loop mask board k 0L rev)

let rec reverse1 put board color =
  let (w,b) = board in
  if color = white then 
    let rev = reverse_sub put (w,b) 0 0L in
    let mboard = logxor w (logor put rev) in
    let oboard = logxor b rev in
    (mboard,oboard)
  else 
    let rev = reverse_sub put (b,w) 7 0L in
    let mboard = logxor b (logor put rev) in
    let oboard = logxor w rev in
    (mboard,oboard)

let rec print_board_sub board =
  let (w,b) = board in
  let mlb = shift_left 1L 63 in (*できれば2^64-1を直接代入したい*)
  if (logand w mlb = mlb) then 
    let w' = shift_left w 1 in
    let b' = shift_left b 1 in
    print_color white;print_string " ";
    (w',b') 
  else if (logand b mlb = mlb) then
    let w' = shift_left w 1 in
    let b' = shift_left b 1 in
    print_color black;print_string " ";
    (w',b') 
  else
    let w' = shift_left w 1 in
    let b' = shift_left b 1 in
    print_color none;print_string " ";
    (w',b') 

let rec print_board_loop board n = 
  if n = 0 then 
  print_endline "\n  (X: Black,  O: White)"
  else 
    if (n mod 8) = 0 then
      let j = 9 - n/8 in
      Printf.printf "\n";
      print_int j; print_string "|";
      let (w',b') = print_board_sub board in
      print_board_loop (w',b') (n-1)
    else 
      let (w',b') = print_board_sub board in
      print_board_loop (w',b') (n-1)

let print_board board = 
  print_endline " |A B C D E F G H ";
  print_endline "-+----------------";
  print_board_loop board 64 