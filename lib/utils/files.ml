
let get_file_content (file_path : string) =
  let ch = open_in_bin file_path in
    let file_content = really_input_string ch (in_channel_length ch) in
    close_in ch;
    file_content

(* let string_to_file (file_path : string) = *)

let get_file_channel (file_path : string) =
  In_channel.open_bin file_path

let write_to_file (file_path : string) (file_content : string) =
  let oc = open_out file_path in
  Printf.fprintf oc "%s\n" file_content;
  close_out oc
