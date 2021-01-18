use super::basic::*;
use std::io;

pub fn main<I: Iterator<Item=String>>(mut args: I) -> Rst<()> 
{
  let tptp = args.next().expect("missing TPTP file");
  let so = io::stdout();
  let mut w = so.lock();

  for i in conv_tptp_file(&tptp) 
  {
      put_char(&mut w, ',')?;
      put_inst(&mut w, &i)?;
  }

  put_char(&mut w, '.')
}
