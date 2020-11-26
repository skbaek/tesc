:- [basic].

create_symlink(PATH, NAME) :- 
  atomic_list_concat([PATH, "/", NAME], DIR), 
  cd(DIR),
  tptp_folder(TPTP),
  atomic_list_concat(["ln -s ", TPTP, "Axioms/ Axioms"], CMD), 
  shell(CMD, _).

symlink :- 
  tptp_folder(TPTP),
  atomic_concat(TPTP, "Problems", PATH),
  folder_folders(PATH, X), 
  writeln_list(X),
  cmap(create_symlink(PATH), X).
