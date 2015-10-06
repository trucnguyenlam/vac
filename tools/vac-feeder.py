#!/usr/bin/env python
'''
    New Script for VAC
'''

import argparse

VACDESCRIPTION = '''
* *                                     VAC 1.0 - 2013-2014                                                   * *
* *              Anna Lisa Ferrara (1), P. Madhusudan (2), Truc L. Nguyen (3), and Gennaro Parlato (3)        * *
* *   (1) University of Bristol (UK), (2) University of Illinois (USA), (3) University of Southampton (UK)    * *
Usage:
  vac-feeder.py [options] INPUT_FILE
Frontend options:                  Purpose:
--no-pruning                        no simplification procedure
--backend=NAME                      choose back-end (interproc, moped, z3, cbmc, eldarica, hsf, nusmv)
--unwind=NUMBER                     unwind NUMBER times (CBMC only)
--print-pruned-policy               print simplified policy only
--print-translated-policy=FORMAT    print the translated program in the format FORMAT (interproc, moped, z3, cbmc, eldarica, hsf, nusmv)
-h, --help                          show help
'''

EPILOG = '''
VAC without any option runs the default option:
first run the abstract transformer followed by Interproc.
If a proof cannot be provided, VAC runs the precise transformer followed by CBMC
(unwind set to 2) to look for a counterexample. Otherwise, it executes Z3 (muZ module) for complete analysis.
'''


def main():
    parser = argparse.ArgumentParser(description=VACDESCRIPTION, epilog=EPILOG)
    parser.add_argument('--no-pruning', help='no simplification procedure', type=str, dest='seq')
    parser.add_argument('-c', '--cex', metavar='X', help='CBMC counter example', type=str, dest='cex')
    parser.add_argument('-r', help='Randomly fix pc', dest='random_switch', default=False, action='store_true')

    args = parser.parse_args()
    if args.random_switch:   #
        fixPCRandomly(args.seq)
    else:
        if args.cex == '':
            print "Please give counter example file from CBMC"
        else:
            fixPCByCBMCCex(args.seq, args.cex)

if __name__ == '__main__':
    main()
