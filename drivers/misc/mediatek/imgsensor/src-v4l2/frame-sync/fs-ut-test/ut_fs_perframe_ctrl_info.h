/* SPDX-License-Identifier: GPL-2.0 */
/*
 * Copyright (c) 2020 MediaTek Inc.
 */

#ifndef _UT_FS_PERFRAME_INFO_H
#define _UT_FS_PERFRAME_INFO_H


/* utility marco */
/**
 *  x : input time in us.
 *  y : put sensor lineTimeInNs value.
 */
#define US_TO_LC(x, y) ((x)*1000/(y)+(((x)*1000%(y))?1:0))


struct ut_fs_perframe_sensor_mode_list {
	char *sensor_name;
	unsigned int sensor_idx;
	struct fs_perframe_st *mode_list;
};


/******************************************************************************/
struct fs_perframe_st imx586_sensor_mode[] = {
	/* Head */
	{
		.sensor_idx = 0,
		.sensor_id = 0x0586,
		.min_fl_lc = US_TO_LC(33350, 10469),
		.shutter_lc = US_TO_LC(19997, 10469),
		.flicker_en = 0,
		.pclk = 752000000,
		.linelength = 7872,
		.margin_lc = 48,
		.lineTimeInNs = 10469,
		.readout_time_us = 31407,
	},

	{
		.sensor_idx = 0,
		.sensor_id = 0x0586,
		.min_fl_lc = US_TO_LC(100000, 10469), // 10 FPS
		.shutter_lc = US_TO_LC(19997, 10469),
		.flicker_en = 0,
		.pclk = 752000000,
		.linelength = 7872,
		.margin_lc = 48,
		.lineTimeInNs = 10469,
		.readout_time_us = 31407,
	},

	{
		.sensor_idx = 0,
		.sensor_id = 0x0586,
		.min_fl_lc = US_TO_LC(200000, 10469), // 5 FPS
		.shutter_lc = US_TO_LC(19997, 10469),
		.flicker_en = 0,
		.pclk = 752000000,
		.linelength = 7872,
		.margin_lc = 48,
		.lineTimeInNs = 10469,
		.readout_time_us = 31407,
	},

	/* End */
	{
		.sensor_idx = -1,
		.sensor_id = 0x0,
		.min_fl_lc = 0,
		.shutter_lc = 0,
		.flicker_en = 0,
		.pclk = 0,
		.linelength = 0,
		.margin_lc = 0,
		.lineTimeInNs = 0,
		.readout_time_us = 0,
	},
};


struct fs_perframe_st s5k3m5sx_sensor_mode[] = {
	/* Head */
	{
		.sensor_idx = 2,
		.sensor_id = 0x30D5,
		.min_fl_lc = US_TO_LC(33350, 10059),
		.shutter_lc = US_TO_LC(19997, 10059),
		.flicker_en = 0,
		.pclk = 482000000,
		.linelength = 4848,
		.margin_lc = 4,
		.lineTimeInNs = 10059,
		.readout_time_us = 31384,
	},

	{
		.sensor_idx = 2,
		.sensor_id = 0x30D5,
		.min_fl_lc = US_TO_LC(100000, 10059), // 10 FPS
		.shutter_lc = US_TO_LC(19997, 10059),
		.flicker_en = 0,
		.pclk = 482000000,
		.linelength = 4848,
		.margin_lc = 4,
		.lineTimeInNs = 10059,
		.readout_time_us = 31384,
	},

	{
		.sensor_idx = 2,
		.sensor_id = 0x30D5,
		.min_fl_lc = US_TO_LC(200000, 10059), // 5 FPS
		.shutter_lc = US_TO_LC(19997, 10059),
		.flicker_en = 0,
		.pclk = 482000000,
		.linelength = 4848,
		.margin_lc = 4,
		.lineTimeInNs = 10059,
		.readout_time_us = 31384,
	},

	/* End */
	{
		.sensor_idx = -1,
		.sensor_id = 0x0,
		.min_fl_lc = 0,
		.shutter_lc = 0,
		.flicker_en = 0,
		.pclk = 0,
		.linelength = 0,
		.margin_lc = 0,
		.lineTimeInNs = 0,
		.readout_time_us = 0,
	},
};


struct fs_perframe_st imx481_sensor_mode[] = {
	/* Head */
	{
		.sensor_idx = 4,
		.sensor_id = 0x0481,
		.min_fl_lc = US_TO_LC(33350, 8828),
		.shutter_lc = US_TO_LC(19997, 8828),
		.flicker_en = 0,
		.pclk = 580000000,
		.linelength = 5120,
		.margin_lc = 18,
		.lineTimeInNs = 8828,
		.readout_time_us = 30863,
	},

	/* End */
	{
		.sensor_idx = -1,
		.sensor_id = 0x0,
		.min_fl_lc = 0,
		.shutter_lc = 0,
		.flicker_en = 0,
		.pclk = 0,
		.linelength = 0,
		.margin_lc = 0,
		.lineTimeInNs = 0,
		.readout_time_us = 0,
	},
};


struct fs_perframe_st imx766_sensor_mode[] = {
	/* Head */
	{
		.sensor_idx = 0,
		.sensor_id = 0x0766,
		.min_fl_lc = US_TO_LC(33350, 6879),
		// .shutter_lc = 0,
		.hdr_exp.mode_exp_cnt = 3,
		.hdr_exp.ae_exp_cnt = 3,
		.hdr_exp.exp_lc = {
			US_TO_LC(10002, 6879),
			US_TO_LC(5000, 6879),
			US_TO_LC(2500, 6879),
			0,
			0
		},
		.flicker_en = 0,
		.pclk = 1281600000,
		.linelength = 8816,
		.margin_lc = 48,
		.lineTimeInNs = 6879,
		.readout_time_us = 32000,
	},

	{
		.sensor_idx = 0,
		.sensor_id = 0x0766,
		.min_fl_lc = US_TO_LC(33350, 6879),
		// .shutter_lc = 0,
		.hdr_exp.mode_exp_cnt = 2,
		.hdr_exp.ae_exp_cnt = 2,
		.hdr_exp.exp_lc = {
			US_TO_LC(10002, 6879),
			US_TO_LC(2500, 6879),
			0,
			0,
			0
		},
		.flicker_en = 0,
		.pclk = 1281600000,
		.linelength = 8816,
		.margin_lc = 48,
		.lineTimeInNs = 6879,
		.readout_time_us = 32000,
	},

	{
		.sensor_idx = 0,
		.sensor_id = 0x0766,
		.min_fl_lc = US_TO_LC(33350, 6879),
		// .shutter_lc = 0,
		.hdr_exp.mode_exp_cnt = 1,
		.hdr_exp.ae_exp_cnt = 1,
		.hdr_exp.exp_lc = {
			US_TO_LC(19997, 6879),
			0,
			0,
			0,
			0
		},
		.flicker_en = 0,
		.pclk = 1281600000,
		.linelength = 8816,
		.margin_lc = 48,
		.lineTimeInNs = 6879,
		.readout_time_us = 32000,
	},

	/* End */
	{
		.sensor_idx = -1,
		.sensor_id = 0x0,
		.min_fl_lc = 0,
		.shutter_lc = 0,
		.flicker_en = 0,
		.pclk = 0,
		.linelength = 0,
		.margin_lc = 0,
		.lineTimeInNs = 0,
		.readout_time_us = 0,
	},
};


struct fs_perframe_st imx516_sensor_mode[] = {
	/* Head */
	{
		.sensor_idx = 4,
		.sensor_id = 0x0516,
		.min_fl_lc = US_TO_LC(33350, 1389),
		.shutter_lc = US_TO_LC(19997, 1389),
		.flicker_en = 0,
		.pclk = 1041120000,
		.linelength = 1446,
		.margin_lc = 1,
		.lineTimeInNs = 1389,
	},

	/* End */
	{
		.sensor_idx = -1,
		.sensor_id = 0x0,
		.min_fl_lc = 0,
		.shutter_lc = 0,
		.flicker_en = 0,
		.pclk = 0,
		.linelength = 0,
		.margin_lc = 0,
		.lineTimeInNs = 0,
		.readout_time_us = 0,
	},
};


/******************************************************************************/
struct ut_fs_perframe_sensor_mode_list ut_fs_pf_s_mode_list[] = {
	/* Head */
	{
		.sensor_name = "imx586",
		.mode_list = imx586_sensor_mode,
	},

	{
		.sensor_name = "s5k3m5sx",
		.mode_list = s5k3m5sx_sensor_mode,
	},

	{
		.sensor_name = "imx481",
		.mode_list = imx481_sensor_mode,
	},

	{
		.sensor_name = "imx766",
		.mode_list = imx766_sensor_mode,
	},

	/* End */
	{
		.sensor_name = "NULL",
		.sensor_idx = -1,
		.mode_list = NULL,
	},
};

#endif
