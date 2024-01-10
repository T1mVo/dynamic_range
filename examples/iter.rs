use std::error::Error;

use dynamic_range::DynamicRange;

fn main() -> Result<(), Box<dyn Error>> {
    let range = DynamicRange::<u8>::try_from("..")?;

    for i in range.into_iter() {
        println!("{i}");
    }

    Ok(())
}
