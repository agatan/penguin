mod primitives;
use primitives::*;

#[cfg(not(test))]
fn main() {
    let non_z = ['1', '2', '3', '4', '5', '6', '7', '8', '9'];
    let non_zero = set(&non_z);
    let digit = select(&exact('0'), &non_zero);
    let dig_head = seq(&seq(&non_zero, &option(&digit)), &option(&digit));
    let dig_tail = seq(&seq(&seq(&exact(','), &digit), &digit), &digit);
    let zero = success(&seq(&exact('0'), &end()));
    let digits = select(&zero, &success(&seq(&seq(&dig_head, &many(&dig_tail)), &end())));

    println!("{:?}", digits);
}
