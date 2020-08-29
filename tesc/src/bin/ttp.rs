use::std::env;
use tptp::parsers::TPTPIterator;
use tptp::syntax::*;
use std::io::{self, StdoutLock};

mod basic;
use basic::*;

fn output_ttp_input(h: &mut StdoutLock, ti: TPTPInput) -> Rst<()> {
  match ti {
    TPTPInput::Annotated(a) => {
      put_char(h, ';')?;
      let (n,f) = conv_annotated_formula(a)?;
      put_nm(h,n)?;
      put_form(h,f)?;
      Ok(())
    },
    TPTPInput::Include(Include {file_name: FileName(SingleQuoted(s)), selection: _}) => {
      let ns: String = format!("{}{}", TPTPPATH, s);
      output_ttp_file(h,&ns)
    }
  }
}

fn output_ttp_file(h: &mut StdoutLock, tptp: &str) -> Rst<()> {
   let bytes = to_boxed_slice(tptp)?;
   let mut is = TPTPIterator::<()>::new(&bytes);
   for x in &mut is {
     match x {
       Ok(i) => output_ttp_input(h,i)?,
       _ => return err_str("Invalid item from TPTP problem file")
     }
   }
   assert!(is.remaining.is_empty());
   Ok(())
}
  
fn main() -> Rst<()> {
  let args: Vec<String> = env::args().collect();
  let tptp = &args[1];

  let stdout = io::stdout();
  let mut handle = stdout.lock();

  output_ttp_file(&mut handle, tptp)?;

  Ok(())
}
