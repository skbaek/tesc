use::std::env;
use tptp::parsers::TPTPIterator;
use tptp::syntax::*;
use std::io::{self};
use std::io::{Write};
use basic::*;

fn output_ttp_input<W: Write>(w: &mut W, ti: TPTPInput) -> Rst<()> {
  match ti {
    TPTPInput::Annotated(a) => {
      put_char(w, ',')?;
      let (n,r,f,a) = conv_annotated_formula(a)?;
      put_string(w,&n)?;
      put_bool(w,r)?;
      put_form(w,&f)?;
      put_option(w,&a)
    },
    TPTPInput::Include(Include {file_name: FileName(SingleQuoted(s)), selection: _}) => {
      let ns: String = format!("{}{}", folders::TPTP, s);
      output_ttp_file(w,&ns)
    }
  }
}

fn output_ttp_file<W: Write>(w: &mut W, tptp: &str) -> Rst<()> {
   let bytes = to_boxed_slice(tptp)?;
   let mut is = TPTPIterator::<()>::new(&bytes);
   for x in &mut is {
     match x {
       Ok(i) => output_ttp_input(w,i)?,
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
  let mut buf = stdout.lock();
  // let mut buf = std::io::BufWriter::new(lock);

  output_ttp_file(&mut buf, tptp)?;
  put_char(&mut buf, '.')
}
