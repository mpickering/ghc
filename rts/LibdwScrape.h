/* ---------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2014-2015
 *
 * Scape DWARF and .debug_ghc information out of loaded modules and place in
 * event log
 *
 * --------------------------------------------------------------------------*/

#ifndef LIBDW_SCRAPE_H
#define LIBDW_SCRAPE_H

int libdwScrapeToEventlog(void);

#endif
