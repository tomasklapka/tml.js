// LICENSE
// This software is free for use and redistribution while including this
// license notice, unless:
// 1. is used for commercial or non-personal purposes, or
// 2. used for a product which includes or associated with a blockchain or other
// decentralized database technology, or
// 3. used for a product which includes or associated with the issuance or use
// of cryptographic or electronic currencies/coins/tokens.
// On all of the mentioned cases, an explicit and written permission is required
// from the Author (Ohad Asor).
// Contact ohad@idni.org for requesting a permission. This license may be
// modified over time by the Author.

// This is a Javascript rewrite of TML by Tomáš Klapka <tomas@klapka.cz>

const { lp, string_read_text } = require('./tml');

// loads string from stream
function load_stream(stream) {
	return new Promise((resolve, reject) => {
		let r = ''; // resulting string
		stream.on('readable', () => { // if we can read
      while ((chunk = stream.read()) !== null)
        r += chunk;     // add stream chunks to string
		});
		stream.on('end', () => resolve(r)); // resolve string
		stream.on('error', reject);         // reject if error
	});
}

// main
async function main() {
	let s;
	try { // read source from stdin
		process.stdin.setEncoding('utf8');
    s = string_read_text(await load_stream(process.stdin));  
	} catch (err) {
		console.log(err);                 // stdin read error
	}
	const p = new lp();                 // new logic program
	p.prog_read(s);                     // parse source
	if (!p.pfp()) console.log('unsat'); // pfp
}

main();
