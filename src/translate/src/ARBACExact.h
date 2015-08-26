#ifndef _ARBACExact_H
#define _ARBACExact_H

#include <string.h>
#include <stdlib.h>
#include "ARBACData.h"
#include "ARBACUtil.h"
#include "ARBACTransform.h"

set * user_config_array;
int user_config_array_size;

int NUM_USER_TO_TRACK;

char*
track_variable_name(int, int);
char*
associate_user_to_track_name(int);
void 
build_config_array();
void 
free_precise_temp_data();

#endif
