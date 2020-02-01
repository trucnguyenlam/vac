#ifndef _ARBACExact_H
#define _ARBACExact_H

#include <string.h>
#include <stdlib.h>
#include "ARBACData.h"
#include "ARBACUtil.h"
#include "ARBACTransform.h"

extern set * user_config_array;
extern int user_config_array_size;

extern int NUM_USER_TO_TRACK;

char*
tracked_user_and_role(int, int);
char*
tracked_user_var(int);
void
build_config_array();
void
free_precise_temp_data();

#endif
