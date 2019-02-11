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
// Author of the Javascript rewrite: Tomáš Klapka <tomas@klapka.cz>

"use strict";

// DEFAULT OPTIONS
const options = {
	recursive: false, // true to use bdds_non_rec ?
}

const { lp, string_read_text } = require("./lp")(options);

// loads string from stream
function load_stream(stream) {
	return new Promise((resolve, reject) => {
		let r = ''; // resulting string
		stream.on('readable', () => { // if we can read
			let chunk;
			while ((chunk = stream.read()) !== null)
				r += chunk;     // add stream chunks to string
		});
		stream.on('end', () => resolve(r)); // resolve string
		stream.on('error', reject);         // reject if error
	});
}

// main
async function main() {
	let s = null;
	//// input for IDE debugging (avoids configuration of stdin)
	// s = "e 1 2. e 2 3. e 3 1. e ?x ?y :- e ?x ?z, e ?z ?y.";
	// s = "father Tom Amy. parent ?X ?Y :- father ?X ?Y.";
	// s = "1 2. 2 1. ?x ?y :- ?y ?x.";
	// unless s, read source from stdin
	if (s === null) {
		try {
			process.stdin.setEncoding('utf8');
			s = string_read_text(await load_stream(process.stdin));
		} catch (err) {   // stdin read error
			console.log('Read error:', err);
			return 4;
		}
	}
	const p = new lp(); // p = logic program
	try {
		p.prog_read(s);   // parse source from s
	} catch (err) {     // parse error
		console.log('Parse error:', err);
		return 3;
	}
	let r = false;
	try {
		r = p.pfp();      // run pfp logic program
	} catch (err) {     // pfp error
		console.log('PFP error', err);
		return 2;
	}
	if (!r) {           // unsat
		console.log('unsat');
	}
	return r ? 0 : 1;
}

module.exports = {
	lp, string_read_text,
	main
};
